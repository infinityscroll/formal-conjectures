import Scratch.A263135ClippingContacts

namespace OeisA263135

/-- The successor of the floor square root of `x-1` is the natural ceiling square root of positive
`x`. -/
theorem isNatCeilSqrt_pred_sqrt_succ (x : ℕ) (hx : 0 < x) :
    IsNatCeilSqrt x ((x - 1).sqrt + 1) := by
  constructor
  · have hs := Nat.sqrt_le' (x - 1)
    simp only [Nat.add_sub_cancel]
    omega
  · have hs := Nat.succ_le_succ_sqrt' (x - 1)
    omega

private def twoVertexWitness : Finset Vertex :=
  {⟨0, 0, false⟩, ⟨0, 0, true⟩}

@[simp]
private theorem card_twoVertexWitness : twoVertexWitness.card = 2 := by
  simp [twoVertexWitness]

@[simp]
private theorem contacts_twoVertexWitness : contacts twoVertexWitness = 1 := by
  norm_num [twoVertexWitness, contacts, neighbor]

/-- Complete even-index extremal theorem for OEIS A263135. -/
@[category research solved, AMS 05]
theorem conjecture_solved (n : ℕ) (hn : 0 < n) :
    ∃ r : ℕ, IsNatCeilSqrt (3 * n) r ∧
      IsMaximumContact (2 * n) (3 * n - r) := by
  let r := (3 * n - 1).sqrt + 1
  have hr : IsNatCeilSqrt (3 * n) r := by
    exact isNatCeilSqrt_pred_sqrt_succ (3 * n) (by positivity)
  refine ⟨r, hr, ?_⟩
  constructor
  · by_cases hn1 : n = 1
    · subst n
      refine ⟨twoVertexWitness, by simp, ?_⟩
      have hr2 : r = 2 := by
        dsimp [r]
        norm_num
      rw [hr2]
      simp
    · have hn2 : 1 < n := by omega
      rcases exists_balanced_clipping_parameters n r hn2 hr with
        ⟨a, b, c, d, ha, hb, hc, hab, hbc, hsum, hM, hd⟩
      refine ⟨clippedPatch a b c d, ?_, ?_⟩
      · rw [card_clippedPatch a b c d ha hb hc hd]
        omega
      · rw [contacts_clippedPatch_formula a b c d ha hb hc hab hd]
        omega
  · intro S hcard
    exact contacts_le_even_closed_form S n r hcard hr

end OeisA263135
