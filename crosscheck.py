#!/usr/bin/env python3
"""Independent cross-check of wowsweep.c invariants on random graphs (n=7)."""
import itertools, random, subprocess, sys
import networkx as nx

def g6(G, n):
    # encode graph6
    bits = []
    for j in range(1, n):
        for i in range(j):
            bits.append(1 if G.has_edge(i, j) else 0)
    while len(bits) % 6: bits.append(0)
    chars = [chr(63 + n)]
    for k in range(0, len(bits), 6):
        v = 0
        for b in bits[k:k+6]: v = v*2 + b
        chars.append(chr(63 + v))
    return ''.join(chars)

def traceable(G, n):
    for perm in itertools.permutations(range(n)):
        if all(G.has_edge(perm[i], perm[i+1]) for i in range(n-1)):
            return True
    return False

def indep_num(G, S):
    best = 0
    S = list(S)
    for r in range(len(S), 0, -1):
        for comb in itertools.combinations(S, r):
            if all(not G.has_edge(a, b) for a, b in itertools.combinations(comb, 2)):
                return r
    return 0

def tree_size(G, n):
    best = 0
    for r in range(n, 0, -1):
        for comb in itertools.combinations(range(n), r):
            H = G.subgraph(comb)
            if nx.is_tree(H): return r
    return 0

def residue(G):
    d = sorted((deg for _, deg in G.degree()), reverse=True)
    while d and d[0] > 0:
        k = d[0]; d = d[1:]
        for i in range(k): d[i] -= 1
        d.sort(reverse=True)
    return len(d)

def gamma2(G, n):
    for r in range(0, n+1):
        for comb in itertools.combinations(range(n), r):
            D = set(comb)
            if all(v in D or sum((u in D) for u in G.neighbors(v)) >= 2 for v in range(n)):
                return r
    return n

def max_leaves_spanning_tree(G, n):
    best = 0
    for T in nx.SpanningTreeIterator(G):
        best = max(best, sum(1 for _, d in T.degree() if d == 1))
        if best == n - 1: break
    return best

random.seed(7)
n = 7
fails = 0
for trial in range(300):
    p = random.uniform(0.2, 0.8)
    G = nx.gnp_random_graph(n, p, seed=trial)
    if not nx.is_connected(G): continue
    s = g6(G, n)
    out = subprocess.run(['./wowsweep', '-D'], input=s+'\n', capture_output=True, text=True).stdout.strip()
    vals = dict(kv.split('=') for kv in out.split())
    lam = {v: indep_num(G, list(G.neighbors(v))) for v in range(n)}
    sumL = sum(lam.values()); lmax = max(lam.values())
    exp = {
        'trace': int(traceable(G, n)),
        'tree': tree_size(G, n),
        'alpha': indep_num(G, range(n)),
        'sumL': sumL,
        'freq': sum(1 for v in lam if lam[v] == lmax),
        'kappa': nx.node_connectivity(G),
        'residue': residue(G),
        'Ls': max_leaves_spanning_tree(G, n),
        'gamma2c': gamma2(nx.complement(G), n),
        'sigma': sorted(d for _, d in G.degree())[1],
        'maxDE': max(sum(1 for u, d in nx.single_source_shortest_path_length(G, v).items() if d % 2 == 0) for v in range(n)),
    }
    for k, v in exp.items():
        if int(vals[k]) != v:
            print(f'MISMATCH trial={trial} {k}: C={vals[k]} py={v} g6={s}')
            fails += 1
print('cross-check done, fails =', fails)
sys.exit(1 if fails else 0)
