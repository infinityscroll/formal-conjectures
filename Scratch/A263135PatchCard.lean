import Scratch.A263135PatchCorners

namespace OeisA263135

/-- Raw boxed triples surviving the central diagonal-row interval. -/
def patchTriples (a b c : ℕ) : Finset ((ℕ × ℕ) × Bool) :=
  (rankBox (a + b) (b + c)).filter fun x =>
    b ≤ rankLevel (tripleRankPoint x) ∧
      rankLevel (tripleRankPoint x) < b + (a + c)

private theorem rankPatch_eq_image_patchTriples (a b c : ℕ) :
    rankPatch a b c = (patchTriples a b c).image tripleRankPoint := by
  rfl

private theorem card_rankBox (A B : ℕ) :
    (rankBox A B).card = 2 * A * B := by
  simp [rankBox, mul_assoc, mul_left_comm, mul_comm]

private theorem lower_middle_disjoint (a b c : ℕ) :
    Disjoint
      ((rankBox (a + b) (b + c)).filter fun x => rankLevel (tripleRankPoint x) < b)
      (patchTriples a b c) := by
  rw [Finset.disjoint_left]
  intro x hl hm
  exact (not_lt_of_ge (Finset.mem_filter.mp hm).2.1) (Finset.mem_filter.mp hl).2

private theorem lower_union_middle (a b c : ℕ) :
    ((rankBox (a + b) (b + c)).filter fun x => rankLevel (tripleRankPoint x) < b) ∪
        patchTriples a b c =
      (rankBox (a + b) (b + c)).filter fun x =>
        rankLevel (tripleRankPoint x) < b + (a + c) := by
  ext x
  simp [patchTriples]
  omega

private theorem below_upper_disjoint (a b c : ℕ) :
    Disjoint
      ((rankBox (a + b) (b + c)).filter fun x =>
        rankLevel (tripleRankPoint x) < b + (a + c))
      (upperCornerTriples (a + b) (b + c) b (a + c)) := by
  rw [Finset.disjoint_left]
  intro x hlo hup
  exact (not_lt_of_ge (Finset.mem_filter.mp hup).2) (Finset.mem_filter.mp hlo).2

private theorem below_union_upper (a b c : ℕ) :
    ((rankBox (a + b) (b + c)).filter fun x =>
        rankLevel (tripleRankPoint x) < b + (a + c)) ∪
      upperCornerTriples (a + b) (b + c) b (a + c) =
        rankBox (a + b) (b + c) := by
  ext x
  simp [upperCornerTriples]
  omega

/-- Cardinality of the convex ranked patch. -/
theorem card_rankPatch (a b c : ℕ) :
    (rankPatch a b c).card = 2 * (a * b + b * c + c * a) := by
  rw [rankPatch_eq_image_patchTriples,
    Finset.card_image_of_injective _ tripleRankPoint_injective]
  have hlower :
      ((rankBox (a + b) (b + c)).filter fun x =>
        rankLevel (tripleRankPoint x) < b).card = b ^ 2 := by
    rw [← lowerCornerTriples_eq_filter_rankBox (a + b) (b + c) b (by omega) (by omega)]
    exact card_lowerCornerTriples b
  have hupper :
      (upperCornerTriples (a + b) (b + c) b (a + c)).card = b ^ 2 := by
    apply card_upperCornerTriples
    · ring
    · omega
    · omega
  have hlowmid := congrArg Finset.card (lower_union_middle a b c)
  rw [Finset.card_union_of_disjoint (lower_middle_disjoint a b c)] at hlowmid
  have htotal := congrArg Finset.card (below_union_upper a b c)
  rw [Finset.card_union_of_disjoint (below_upper_disjoint a b c)] at htotal
  rw [card_rankBox] at htotal
  nlinarith

/-- Cardinality of the concrete honeycomb patch. -/
theorem card_patch_formula (a b c : ℕ) :
    (patch a b c).card = 2 * (a * b + b * c + c * a) := by
  rw [card_patch, card_rankPatch]

end OeisA263135
