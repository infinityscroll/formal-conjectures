/* wowsweep.c — sweep connected graphs (graph6 on stdin, from geng -cq) for
 * counterexamples to WOWII Hamiltonian-path conjectures 189,194,199,200,209,213,217.
 *
 * A counterexample = graph satisfying the conjecture's premise and having NO
 * Hamiltonian path. All conjectures share the conclusion "G is traceable",
 * so we first decide traceability (cheap greedy, exact DP fallback) and only
 * compute invariants for non-traceable survivors.
 *
 * Invariant definitions follow DeLaVina's WOWII definitions page and the
 * google-deepmind/formal-conjectures formalizations:
 *   lambda(v)  = independence number of G[N(v)]
 *   l_avg      = (sum_v lambda(v)) / n
 *   tree(G)    = max |S| over S inducing a tree (connected, |E|=|S|-1)
 *   alpha      = independence number
 *   kappa      = vertex connectivity
 *   sigma(G)   = second smallest degree (WOWII def 65)
 *   distEven(v)= #vertices at even distance from v (0 counts; variant B excludes v)
 *   freqLmax   = #vertices attaining max lambda(v)
 *   residue    = Havel-Hakimi residue
 *   Ls         = max leaves over spanning trees = n - gamma_c (n>=3)
 *   gamma2     = 2-domination number
 * Premises (integer arithmetic, no floats):
 *   189: max distEven(v) <= 1 + sigma(G)
 *   194: n*alpha <= n + sumLambda
 *   199: tree - 2 <= kappa
 *   200: tree == ceil((n+sumLambda)/n)
 *   209: 1 + 2*|E(complement)| <= 6*freqLmax
 *   213: 2 + lowerMedianDeg(complement) <= gamma2(complement)
 *   217: Ls <= 4*[residue==2] + 2
 * Output: "<conj> <graph6> leaves=<k> twoconn=<0|1>" per hit.
 * With -T runs self-tests and exits.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 12
static int N;                 /* current graph order */
static uint16_t adj[MAXN];    /* adjacency bitmasks */
static uint16_t FULL;

/* ---------- graph6 ---------- */
static int parse_g6(const char *s, int expect_n) {
    int n = s[0] - 63;
    if (n < 1 || n > MAXN) return -1;
    if (expect_n && n != expect_n) return -1;
    N = n; FULL = (uint16_t)((1u << n) - 1);
    memset(adj, 0, sizeof adj);
    int bitpos = 0;
    const char *p = s + 1;
    for (int j = 1; j < n; j++)
        for (int i = 0; i < j; i++, bitpos++) {
            int byte = bitpos / 6, off = 5 - bitpos % 6;
            if (((p[byte] - 63) >> off) & 1) {
                adj[i] |= (uint16_t)(1u << j);
                adj[j] |= (uint16_t)(1u << i);
            }
        }
    return n;
}

static inline int pc(uint32_t x) { return __builtin_popcount(x); }

/* ---------- traceability ---------- */
/* exact: reach[mask] = set of possible endpoints of a simple path on exactly mask */
static uint16_t reach[1 << MAXN];
static int traceable_exact(void) {
    for (int v = 0; v < N; v++) reach[1u << v] = (uint16_t)(1u << v);
    uint32_t full = FULL;
    for (uint32_t m = 1; m <= full; m++) {
        if (pc(m) < 2) continue;
        uint16_t r = 0;
        uint32_t mm = m;
        while (mm) {
            uint32_t v = __builtin_ctz(mm); mm &= mm - 1;
            uint32_t prev = m & ~(1u << v);
            if (reach[prev] & adj[v]) r |= (uint16_t)(1u << v);
        }
        reach[m] = r;
        if (m == full && r) return 1;
    }
    return reach[full] != 0;
}
/* greedy: extend a path at both ends, min-degree-first tie-break */
static int greedy_from(int s) {
    int path[MAXN], head, tail;
    uint16_t used = (uint16_t)(1u << s);
    path[0] = s; head = tail = 0;
    while (pc(used) < N) {
        /* try extend tail then head, pick unvisited neighbor with min remaining degree */
        int best = -1, bestd = 99, endsel = -1;
        for (int e = 0; e < 2; e++) {
            int end = e ? path[head] : path[tail];
            uint16_t cand = adj[end] & ~used;
            while (cand) {
                int v = __builtin_ctz(cand); cand &= (uint16_t)(cand - 1);
                int d = pc(adj[v] & ~used);
                if (d < bestd) { bestd = d; best = v; endsel = e; }
            }
        }
        if (best < 0) return 0;
        used |= (uint16_t)(1u << best);
        if (endsel) { /* extend head side: shift not needed, keep two indices in array trick */
            /* store path in a deque-like array: we simulate with fixed array centered */
            /* simpler: rebuild not needed; we only track endpoints */
            path[head = (head + 1) % MAXN] = best; /* head pointer reused as slot */
        } else {
            path[tail = (tail + MAXN - 1) % MAXN] = best;
        }
    }
    return 1;
}
static int traceable(void) {
    /* >=3 leaves => not traceable; but only when N>2 */
    if (N > 2) {
        int leaves = 0;
        for (int v = 0; v < N; v++) if (pc(adj[v]) == 1) leaves++;
        if (leaves >= 3) return 0;
    }
    /* greedy attempts from up to 3 lowest-degree vertices */
    int order[MAXN];
    for (int v = 0; v < N; v++) order[v] = v;
    for (int a = 0; a < N; a++)
        for (int b = a + 1; b < N; b++)
            if (pc(adj[order[b]]) < pc(adj[order[a]])) { int t = order[a]; order[a] = order[b]; order[b] = t; }
    int tries = N < 3 ? N : 3;
    for (int i = 0; i < tries; i++)
        if (greedy_from(order[i])) return 1;
    return traceable_exact();
}

/* ---------- subset sweep ---------- */
static uint8_t edges_[1 << MAXN];
static uint8_t conn_[1 << MAXN];
static void sweep(void) {
    edges_[0] = 0; conn_[0] = 0;
    for (uint32_t m = 1; m <= FULL; m++) {
        uint32_t low = m & (uint32_t)(-(int32_t)m);
        int v = __builtin_ctz(low);
        uint32_t rest = m ^ low;
        edges_[m] = (uint8_t)(edges_[rest] + pc(adj[v] & rest));
        /* connectivity by BFS from v inside m */
        uint32_t comp = low, frontier = low;
        while (frontier) {
            uint32_t nf = 0, f = frontier;
            while (f) {
                int u = __builtin_ctz(f); f &= f - 1;
                nf |= adj[u] & m & ~comp;
            }
            comp |= nf; frontier = nf;
        }
        conn_[m] = (comp == m);
    }
}

/* Havel–Hakimi residue */
static int residue(void) {
    int d[MAXN];
    for (int v = 0; v < N; v++) d[v] = pc(adj[v]);
    int n = N;
    for (;;) {
        /* sort descending */
        for (int a = 0; a < n; a++)
            for (int b = a + 1; b < n; b++)
                if (d[b] > d[a]) { int t = d[a]; d[a] = d[b]; d[b] = t; }
        if (d[0] == 0) return n;
        int k = d[0];
        for (int i = 1; i <= k && i < n; i++) d[i]--;
        for (int i = 0; i < n - 1; i++) d[i] = d[i + 1];
        n--;
    }
}

int main(int argc, char **argv) {
    int expect_n = 0, selftest = 0, debug = 0;
    for (int a = 1; a < argc; a++) {
        if (!strcmp(argv[a], "-T")) selftest = 1;
        else if (!strcmp(argv[a], "-D")) debug = 1;
        else expect_n = atoi(argv[a]);
    }
    char line[64];
    long total = 0, nontrace = 0;

    const char *tests[] = {
        "J??FFBRq}N_",   /* 11v counterexample to 200: premise200, not traceable */
        "DhC",           /* P5? placeholder, replaced in tests below */
        NULL };
    (void)tests;
    if (selftest) {
        /* K4: complete on 4 vertices: g6 "C~" */
        parse_g6("C~", 0);
        if (!traceable()) { printf("FAIL K4 traceable\n"); return 1; }
        /* star K1,3: "Cs" = ? build manually instead */
        N = 4; FULL = 15; memset(adj, 0, sizeof adj);
        adj[0] = 0b1110; adj[1] = 1; adj[2] = 1; adj[3] = 1;
        if (traceable()) { printf("FAIL star nontraceable\n"); return 1; }
        /* known 200-counterexample */
        if (parse_g6("J??FFBRq}N_", 0) != 11) { printf("FAIL parse\n"); return 1; }
        if (traceable()) { printf("FAIL cex nontraceable\n"); return 1; }
        sweep();
        /* invariants */
        int sumL = 0, lmax = 0;
        for (int v = 0; v < N; v++) {
            int best = 0;
            uint32_t nb = adj[v];
            for (uint32_t s = nb; ; s = (s - 1) & nb) {
                if (edges_[s] == 0 && pc(s) > best) best = pc(s);
                if (s == 0) break;
            }
            sumL += best; if (best > lmax) lmax = best;
        }
        int tree = 0, alpha = 0;
        for (uint32_t m = 1; m <= FULL; m++) {
            int p = pc(m);
            if (edges_[m] == 0 && p > alpha) alpha = p;
            if (conn_[m] && edges_[m] == p - 1 && p > tree) tree = p;
        }
        int ceil200 = (N + sumL + N - 1) / N;
        printf("selftest cex: sumLambda=%d (want 24) tree=%d (want 4) ceil=%d (want 4) alpha=%d (want 6) residue=%d\n",
               sumL, tree, ceil200, alpha, residue());
        if (sumL != 24 || tree != 4 || ceil200 != 4 || alpha != 6) { printf("FAIL invariants\n"); return 1; }
        /* P4 path 0-1-2-3 */
        N = 4; FULL = 15; memset(adj, 0, sizeof adj);
        adj[0] = 2; adj[1] = 5; adj[2] = 10; adj[3] = 4;
        if (!traceable()) { printf("FAIL P4\n"); return 1; }
        printf("selftest OK\n");
        return 0;
    }

    while (fgets(line, sizeof line, stdin)) {
        size_t L = strlen(line);
        while (L && (line[L-1] == '\n' || line[L-1] == '\r')) line[--L] = 0;
        if (!L) continue;
        if (parse_g6(line, expect_n) < 0) { fprintf(stderr, "bad g6: %s\n", line); continue; }
        total++;
        int trace = traceable();
        if (!debug && trace) continue;
        nontrace += !trace;
        sweep();

        int deg[MAXN], leaves = 0;
        for (int v = 0; v < N; v++) { deg[v] = pc(adj[v]); if (deg[v] == 1) leaves++; }

        /* lambda(v), sums */
        int sumL = 0, lmax = 0;
        int lam[MAXN];
        for (int v = 0; v < N; v++) {
            int best = 0; uint32_t nb = adj[v];
            for (uint32_t s = nb; ; s = (s - 1) & nb) {
                if (edges_[s] == 0 && pc(s) > best) best = pc(s);
                if (s == 0) break;
            }
            lam[v] = best; sumL += best; if (best > lmax) lmax = best;
        }
        int freq = 0;
        for (int v = 0; v < N; v++) if (lam[v] == lmax) freq++;

        int tree = 0, alpha = 0, maxDisc = 0, gammaC = N + 1;
        for (uint32_t m = 1; m <= FULL; m++) {
            int p = pc(m);
            if (edges_[m] == 0 && p > alpha) alpha = p;
            if (conn_[m]) {
                if (edges_[m] == p - 1 && p > tree) tree = p;
                /* dominating? */
                uint32_t dom = m, mm = m;
                while (mm) { int u = __builtin_ctz(mm); mm &= mm - 1; dom |= adj[u]; }
                if (dom == FULL && p < gammaC) gammaC = p;
            } else if (p >= 2 && p > maxDisc) maxDisc = p;
        }
        int kappa = maxDisc ? N - maxDisc : N - 1;
        int Ls = N - gammaC;

        /* BFS distances -> distEven */
        int maxDE_incl = 0, maxDE_excl = 0;
        for (int v = 0; v < N; v++) {
            int dist[MAXN]; for (int u = 0; u < N; u++) dist[u] = -1;
            dist[v] = 0; uint32_t fr = 1u << v; int dcur = 0;
            uint32_t seen = fr;
            while (fr) {
                uint32_t nf = 0, f = fr;
                while (f) { int u = __builtin_ctz(f); f &= f - 1; nf |= adj[u] & ~seen; }
                dcur++;
                uint32_t f2 = nf; while (f2) { int u = __builtin_ctz(f2); f2 &= f2 - 1; dist[u] = dcur; }
                seen |= nf; fr = nf;
            }
            int de = 0;
            for (int u = 0; u < N; u++) if (dist[u] >= 0 && dist[u] % 2 == 0) de++;
            if (de > maxDE_incl) maxDE_incl = de;
            if (de - 1 > maxDE_excl) maxDE_excl = de - 1;
        }
        /* sigma = 2nd smallest degree */
        int sd[MAXN]; memcpy(sd, deg, sizeof sd);
        for (int a = 0; a < N; a++) for (int b = a + 1; b < N; b++) if (sd[b] < sd[a]) { int t = sd[a]; sd[a] = sd[b]; sd[b] = t; }
        int sigma = sd[1];

        /* complement invariants for 209/213 */
        uint16_t cadj[MAXN];
        for (int v = 0; v < N; v++) cadj[v] = (uint16_t)(FULL & ~adj[v] & ~(1u << v));
        int ecomp = 0, cdeg[MAXN];
        for (int v = 0; v < N; v++) { cdeg[v] = pc(cadj[v]); ecomp += cdeg[v]; }
        ecomp /= 2;
        int csd[MAXN]; memcpy(csd, cdeg, sizeof csd);
        for (int a = 0; a < N; a++) for (int b = a + 1; b < N; b++) if (csd[b] < csd[a]) { int t = csd[a]; csd[a] = csd[b]; csd[b] = t; }
        int lowerMedC = (N % 2) ? csd[(N - 1) / 2] : csd[N / 2 - 1];
        /* gamma2 of complement: every vertex not in D has >=2 complement-neighbors in D */
        int gamma2c = N;
        for (uint32_t m = 0; m <= FULL; m++) {
            int p = pc(m); if (p >= gamma2c) continue;
            int ok = 1;
            for (int v = 0; v < N && ok; v++)
                if (!((m >> v) & 1) && pc(cadj[v] & m) < 2) ok = 0;
            if (ok) gamma2c = p;
        }
        int res = residue();

        int twoconn = (kappa >= 2);
        int ceil200 = (N + sumL + N - 1) / N;

        if (debug) {
            printf("trace=%d tree=%d alpha=%d sumL=%d freq=%d kappa=%d residue=%d Ls=%d gamma2c=%d sigma=%d maxDE=%d\n",
                   trace, tree, alpha, sumL, freq, kappa, res, Ls, gamma2c, sigma, maxDE_incl);
            continue;
        }

        if (maxDE_incl <= 1 + sigma)
            printf("189 %s leaves=%d twoconn=%d\n", line, leaves, twoconn);
        if (maxDE_excl <= 1 + sigma)
            printf("189B %s leaves=%d twoconn=%d\n", line, leaves, twoconn);
        if (N * alpha <= N + sumL)
            printf("194 %s leaves=%d twoconn=%d\n", line, leaves, twoconn);
        if (tree - 2 <= kappa)
            printf("199 %s leaves=%d twoconn=%d\n", line, leaves, twoconn);
        if (tree == ceil200)
            printf("200 %s leaves=%d twoconn=%d\n", line, leaves, twoconn);
        if (1 + 2 * ecomp <= 6 * freq)
            printf("209 %s leaves=%d twoconn=%d\n", line, leaves, twoconn);
        if (2 + lowerMedC <= gamma2c)
            printf("213 %s leaves=%d twoconn=%d\n", line, leaves, twoconn);
        if (Ls <= 4 * (res == 2 ? 1 : 0) + 2)
            printf("217 %s leaves=%d twoconn=%d\n", line, leaves, twoconn);
    }
    fprintf(stderr, "done: total=%ld nontraceable=%ld\n", total, nontrace);
    return 0;
}
