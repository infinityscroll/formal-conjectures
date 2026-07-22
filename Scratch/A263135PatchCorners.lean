import Scratch.A263135PatchDefs

namespace OeisA263135

/-- Natural-coordinate pairs strictly below diagonal level `b`. -/
def lowerPairs (b : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range b).biUnion Finset.Nat.antidiagonal

@[simp]
theorem mem_lowerPairs {b i j : ℕ} :
    (i, j) ∈ lowerPairs b ↔ i + j < b := by
  constructor
  · intro h
    rcases Finset.mem_biUnion.mp h with ⟨n, hn, hij⟩
    have hs := Finset.mem_antidiagonal.mp hij
    omega
  · intro h
    apply Finset.mem_biUnion.mpr
    exact ⟨i + j, Finset.mem_range.mpr h, Finset.mem_antidiagonal.mpr rfl⟩

private theorem antidiagonal_pairwise_disjoint (b : ℕ) :
    (Finset.range b).toSet.PairwiseDisjoint Finset.Nat.antidiagonal := by
  intro m hm n hn hmn
  rw [Finset.disjoint_left]
  intro p hpm hpn
  have hm' := Finset.mem_antidiagonal.mp hpm
  have hn' := Finset.mem_antidiagonal.mp hpn
  exact hmn (hm'.symm.trans hn')

/-- Cardinality of the strict lower triangle as a sum of antidiagonal sizes. -/
theorem card_lowerPairs (b : ℕ) :
    (lowerPairs b).card = ∑ n ∈ Finset.range b, (n + 1) := by
  rw [lowerPairs, Finset.card_biUnion]
  · simp
  · exact antidiagonal_pairwise_disjoint b

/-- Lower excluded corner of a rank box, split by honeycomb side. -/
def lowerCornerTriples (b : ℕ) : Finset ((ℕ × ℕ) × Bool) :=
  (lowerPairs b ×ˢ {false}) ∪ (lowerPairs (b - 1) ×ˢ {true})

private theorem lower_corner_sides_disjoint (b : ℕ) :
    Disjoint (lowerPairs b ×ˢ {false}) (lowerPairs (b - 1) ×ˢ {true}) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  have hf := (Finset.mem_product.mp hx).2
  have ht := (Finset.mem_product.mp hy).2
  simp at hf ht

/-- The lower excluded corner contains exactly `b²` ranked points. -/
theorem card_lowerCornerTriples (b : ℕ) :
    (lowerCornerTriples b).card = b ^ 2 := by
  rw [lowerCornerTriples,
    Finset.card_union_of_disjoint (lower_corner_sides_disjoint b)]
  simp only [Finset.card_product, Finset.card_singleton, mul_one,
    card_lowerPairs]
  by_cases hb : b = 0
  · subst b
    simp
  · have hb1 : 1 ≤ b := Nat.one_le_iff_ne_zero.mpr hb
    have hgauss1 := Finset.sum_range_id_mul_two b
    have hgauss2 := Finset.sum_range_id_mul_two (b - 1)
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      Nat.nsmul_eq_mul, mul_one] at *
    nlinarith

/-- The lower-corner description agrees with filtering any sufficiently large box by level. -/
theorem lowerCornerTriples_eq_filter_rankBox
    (A B b : ℕ) (hbA : b ≤ A) (hbB : b ≤ B) :
    lowerCornerTriples b =
      (rankBox A B).filter fun x => rankLevel (tripleRankPoint x) < b := by
  ext x
  rcases x with ⟨⟨i, j⟩, side⟩
  cases side <;>
    simp [lowerCornerTriples, rankBox, rankLevel, tripleRankPoint, mem_lowerPairs] <;>
    omega

/-- Central reflection of a finite rank box. -/
def reflectTriple (A B : ℕ) (x : (ℕ × ℕ) × Bool) : (ℕ × ℕ) × Bool :=
  ((A - 1 - x.1.1, B - 1 - x.1.2), !x.2)

private theorem reflectTriple_involutive_on_box
    {A B : ℕ} {x : (ℕ × ℕ) × Bool} (hx : x ∈ rankBox A B) :
    reflectTriple A B (reflectTriple A B x) = x := by
  rcases x with ⟨⟨i, j⟩, side⟩
  simp [rankBox] at hx
  rcases hx with ⟨hi, hj⟩
  apply Prod.ext
  · apply Prod.ext <;> simp [reflectTriple] <;> omega
  · simp [reflectTriple]

private theorem reflectTriple_mem_box
    {A B : ℕ} {x : (ℕ × ℕ) × Bool} (hx : x ∈ rankBox A B) :
    reflectTriple A B x ∈ rankBox A B := by
  rcases x with ⟨⟨i, j⟩, side⟩
  simp [rankBox] at hx ⊢
  omega

/-- Upper excluded corner of the patch interval. -/
def upperCornerTriples (A B b C : ℕ) : Finset ((ℕ × ℕ) × Bool) :=
  (rankBox A B).filter fun x => b + C ≤ rankLevel (tripleRankPoint x)

/-- Reflection maps the upper corner bijectively to the lower corner when `A+B=C+2b`. -/
theorem card_upperCornerTriples
    (A B b C : ℕ) (hsum : A + B = C + 2 * b) (hbA : b ≤ A) (hbB : b ≤ B) :
    (upperCornerTriples A B b C).card = b ^ 2 := by
  have htarget := lowerCornerTriples_eq_filter_rankBox A B b hbA hbB
  rw [← htarget, ← card_lowerCornerTriples b]
  apply Finset.card_bij (fun x hx => reflectTriple A B x)
  · intro x hx
    have hxbox := (Finset.mem_filter.mp hx).1
    have hxupper := (Finset.mem_filter.mp hx).2
    rw [lowerCornerTriples_eq_filter_rankBox A B b hbA hbB]
    apply Finset.mem_filter.mpr
    refine ⟨reflectTriple_mem_box hxbox, ?_⟩
    rcases x with ⟨⟨i, j⟩, side⟩
    cases side <;> simp [reflectTriple, rankLevel, tripleRankPoint] at hxbox hxupper ⊢ <;> omega
  · intro x hx y hy hxy
    have hxbox := (Finset.mem_filter.mp hx).1
    have hybox := (Finset.mem_filter.mp hy).1
    rw [← reflectTriple_involutive_on_box hxbox,
      ← reflectTriple_involutive_on_box hybox, hxy]
  · intro y hy
    rw [lowerCornerTriples_eq_filter_rankBox A B b hbA hbB] at hy
    have hybox := (Finset.mem_filter.mp hy).1
    refine ⟨reflectTriple A B y, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨reflectTriple_mem_box hybox, ?_⟩
      have hylower := (Finset.mem_filter.mp hy).2
      rcases y with ⟨⟨i, j⟩, side⟩
      cases side <;> simp [reflectTriple, rankLevel, tripleRankPoint] at hybox hylower ⊢ <;> omega
    · exact reflectTriple_involutive_on_box hybox

end OeisA263135
