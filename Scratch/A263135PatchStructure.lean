import Scratch.A263135PatchCard

namespace OeisA263135

@[simp]
theorem mem_rankPatch {a b c : ℕ} {p : RankPoint} :
    p ∈ rankPatch a b c ↔
      p.first < a + b ∧ p.second < b + c ∧
        b ≤ rankLevel p ∧ rankLevel p < b + (a + c) := by
  constructor
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨x, hx, rfl⟩
    rcases Finset.mem_filter.mp hx with ⟨hbox, hlev⟩
    rcases x with ⟨⟨i, j⟩, side⟩
    simpa [rankBox, tripleRankPoint] using And.intro hbox hlev
  · rintro ⟨hi, hj, hlo, hhi⟩
    let x : (ℕ × ℕ) × Bool := ((p.first, p.second), p.side)
    apply Finset.mem_image.mpr
    refine ⟨x, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      exact ⟨by simp [rankBox, x, hi, hj], by simpa [x, tripleRankPoint]⟩
    · rcases p with ⟨i, j, side⟩
      rfl

@[simp]
theorem rankPointVertex_mem_patch_iff {a b c : ℕ} {p : RankPoint} :
    rankPointVertex p ∈ patch a b c ↔ p ∈ rankPatch a b c := by
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨q, hq, heq⟩
    exact rankPointVertex_injective heq ▸ hq
  · exact fun h => Finset.mem_image.mpr ⟨p, h, rfl⟩

/-- A-side ranked vertices in a patch. -/
def aRankPatch (a b c : ℕ) : Finset RankPoint :=
  (rankPatch a b c).filter fun p => p.side = false

/-- B-side ranked vertices in a patch. -/
def bRankPatch (a b c : ℕ) : Finset RankPoint :=
  (rankPatch a b c).filter fun p => p.side = true

private theorem a_b_rankPatch_disjoint (a b c : ℕ) :
    Disjoint (aRankPatch a b c) (bRankPatch a b c) := by
  rw [Finset.disjoint_left]
  intro p ha hb
  have hf := (Finset.mem_filter.mp ha).2
  have ht := (Finset.mem_filter.mp hb).2
  simp [hf] at ht

private theorem a_union_b_rankPatch (a b c : ℕ) :
    aRankPatch a b c ∪ bRankPatch a b c = rankPatch a b c := by
  ext p
  simp [aRankPatch, bRankPatch]
  cases h : p.side <;> simp [h]

/-- Central reflection of ranked patch coordinates. -/
def reflectRankPoint (a b c : ℕ) (p : RankPoint) : RankPoint :=
  ⟨a + b - 1 - p.first, b + c - 1 - p.second, !p.side⟩

private theorem reflectRankPoint_mem
    {a b c : ℕ} {p : RankPoint} (hp : p ∈ rankPatch a b c) :
    reflectRankPoint a b c p ∈ rankPatch a b c := by
  rw [mem_rankPatch] at hp ⊢
  rcases p with ⟨i, j, side⟩
  cases side <;> simp [reflectRankPoint, rankLevel] at hp ⊢ <;> omega

private theorem reflectRankPoint_involutive
    {a b c : ℕ} {p : RankPoint} (hp : p ∈ rankPatch a b c) :
    reflectRankPoint a b c (reflectRankPoint a b c p) = p := by
  rw [mem_rankPatch] at hp
  rcases p with ⟨i, j, side⟩
  simp [reflectRankPoint]
  omega

/-- The two bipartite sides of a convex patch have equal cardinality. -/
theorem card_aRankPatch_eq_card_bRankPatch (a b c : ℕ) :
    (aRankPatch a b c).card = (bRankPatch a b c).card := by
  apply Finset.card_bij (fun p hp => reflectRankPoint a b c p)
  · intro p hp
    apply Finset.mem_filter.mpr
    refine ⟨reflectRankPoint_mem (Finset.mem_filter.mp hp).1, ?_⟩
    simpa [reflectRankPoint, (Finset.mem_filter.mp hp).2]
  · intro p hp q hq h
    rw [← reflectRankPoint_involutive (Finset.mem_filter.mp hp).1,
      ← reflectRankPoint_involutive (Finset.mem_filter.mp hq).1, h]
  · intro q hq
    refine ⟨reflectRankPoint a b c q, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨reflectRankPoint_mem (Finset.mem_filter.mp hq).1, ?_⟩
      simpa [reflectRankPoint, (Finset.mem_filter.mp hq).2]
    · exact reflectRankPoint_involutive (Finset.mem_filter.mp hq).1

/-- Each bipartite side has `ab+bc+ca` vertices. -/
theorem card_aRankPatch (a b c : ℕ) :
    (aRankPatch a b c).card = a * b + b * c + c * a := by
  have htotal := congrArg Finset.card (a_union_b_rankPatch a b c)
  rw [Finset.card_union_of_disjoint (a_b_rankPatch_disjoint a b c),
    card_rankPatch, card_aRankPatch_eq_card_bRankPatch] at htotal
  omega

/-- A-side vertices on the top diagonal row. -/
def topARankPatch (a b c : ℕ) : Finset RankPoint :=
  (aRankPatch a b c).filter fun p => rankLevel p = a + b + c - 1

/-- A-side vertices on the first-coordinate boundary. -/
def firstZeroARankPatch (a b c : ℕ) : Finset RankPoint :=
  (aRankPatch a b c).filter fun p => p.first = 0

/-- A-side vertices on the second-coordinate boundary. -/
def secondZeroARankPatch (a b c : ℕ) : Finset RankPoint :=
  (aRankPatch a b c).filter fun p => p.second = 0

/-- The top A-side row has length `b`. -/
theorem card_topARankPatch (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (topARankPatch a b c).card = b := by
  conv_rhs => rw [← Finset.card_range b]
  symm
  apply Finset.card_bij (fun k hk => (⟨a + k, b + c - 1 - k, false⟩ : RankPoint))
  · intro k hk
    have hk' := Finset.mem_range.mp hk
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨?_, rfl⟩, ?_⟩
    · rw [mem_rankPatch]
      simp [rankLevel]
      omega
    · simp [rankLevel]
      omega
  · intro k hk l hl h
    have := congrArg RankPoint.first h
    omega
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨haP, htop⟩
    rcases Finset.mem_filter.mp haP with ⟨hpatch, hside⟩
    rw [mem_rankPatch] at hpatch
    rcases p with ⟨i, j, side⟩
    simp [rankLevel] at hside htop hpatch
    refine ⟨i - a, Finset.mem_range.mpr (by omega), ?_⟩
    apply RankPoint.ext <;> simp <;> omega

/-- The first-coordinate A-side boundary has length `c`. -/
theorem card_firstZeroARankPatch (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (firstZeroARankPatch a b c).card = c := by
  conv_rhs => rw [← Finset.card_range c]
  symm
  apply Finset.card_bij (fun k hk => (⟨0, b + k, false⟩ : RankPoint))
  · intro k hk
    have hk' := Finset.mem_range.mp hk
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨?_, rfl⟩, rfl⟩
    rw [mem_rankPatch]
    simp [rankLevel]
    omega
  · intro k hk l hl h
    have := congrArg RankPoint.second h
    omega
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨haP, hfirst⟩
    rcases Finset.mem_filter.mp haP with ⟨hpatch, hside⟩
    rw [mem_rankPatch] at hpatch
    rcases p with ⟨i, j, side⟩
    simp [rankLevel] at hfirst hside hpatch
    refine ⟨j - b, Finset.mem_range.mpr (by omega), ?_⟩
    apply RankPoint.ext <;> simp <;> omega

/-- The second-coordinate A-side boundary has length `a`. -/
theorem card_secondZeroARankPatch (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (secondZeroARankPatch a b c).card = a := by
  conv_rhs => rw [← Finset.card_range a]
  symm
  apply Finset.card_bij (fun k hk => (⟨b + k, 0, false⟩ : RankPoint))
  · intro k hk
    have hk' := Finset.mem_range.mp hk
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨?_, rfl⟩, rfl⟩
    rw [mem_rankPatch]
    simp [rankLevel]
    omega
  · intro k hk l hl h
    have := congrArg RankPoint.first h
    omega
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨haP, hsecond⟩
    rcases Finset.mem_filter.mp haP with ⟨hpatch, hside⟩
    rw [mem_rankPatch] at hpatch
    rcases p with ⟨i, j, side⟩
    simp [rankLevel] at hsecond hside hpatch
    refine ⟨i - b, Finset.mem_range.mpr (by omega), ?_⟩
    apply RankPoint.ext <;> simp <;> omega

end OeisA263135
