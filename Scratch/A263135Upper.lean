import Scratch.A263135Incidence

namespace OeisA263135

/-- The edge boundary of an even-cardinality honeycomb set is even. -/
theorem edgeBoundary_even_of_card_eq_two_mul
    (S : Finset Vertex) (n : ℕ) (hcard : S.card = 2 * n) :
    Even (edgeBoundary S) := by
  have hinc := three_mul_card_eq_two_mul_contacts_add_boundary S
  rw [hcard] at hinc
  have hc : contacts S ≤ 3 * n := by omega
  refine ⟨3 * n - contacts S, ?_⟩
  omega

/-- Boundary lower bound at even cardinality. -/
theorem two_mul_ceilSqrt_le_edgeBoundary
    (S : Finset Vertex) (n r : ℕ)
    (hcard : S.card = 2 * n)
    (hr : IsNatCeilSqrt (3 * n) r) :
    2 * r ≤ edgeBoundary S := by
  let R := (occupiedRows .first S).card + (occupiedRows .second S).card +
    (occupiedRows .diagonal S).card
  have hrow : R ≤ edgeBoundary S := by
    simpa [R] using sum_occupiedRows_card_le_edgeBoundary S
  have hquad := six_mul_card_le_row_sum_sq S
  rw [hcard] at hquad
  have hboundarySq : 12 * n ≤ (edgeBoundary S) ^ 2 := by
    have hsq : R ^ 2 ≤ (edgeBoundary S) ^ 2 := by
      nlinarith
    nlinarith
  rcases edgeBoundary_even_of_card_eq_two_mul S n hcard with ⟨q, hq⟩
  have hqSq : 3 * n ≤ q ^ 2 := by
    rw [hq] at hboundarySq
    nlinarith
  have hrq : r ≤ q := by
    by_contra h
    have hqr : q ≤ r - 1 := by omega
    have hsquares : q ^ 2 ≤ (r - 1) ^ 2 := by
      nlinarith
    exact (not_lt_of_ge (hqSq.trans hsquares)) hr.1
  rw [hq]
  omega

/-- Universal half of the even-index A263135 closed form. -/
theorem contacts_le_even_closed_form
    (S : Finset Vertex) (n r : ℕ)
    (hcard : S.card = 2 * n)
    (hr : IsNatCeilSqrt (3 * n) r) :
    contacts S ≤ 3 * n - r := by
  have hboundary := two_mul_ceilSqrt_le_edgeBoundary S n r hcard hr
  have hinc := three_mul_card_eq_two_mul_contacts_add_boundary S
  rw [hcard] at hinc
  omega

end OeisA263135
