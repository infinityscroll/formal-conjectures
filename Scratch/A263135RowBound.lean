import Scratch.A263135Endpoints

namespace OeisA263135

/-- The edge boundary dominates the sum of the three occupied-row counts. -/
theorem sum_occupiedRows_card_le_edgeBoundary (S : Finset Vertex) :
    (∑ r : RowKind, (occupiedRows r S).card) ≤ edgeBoundary S := by
  have hsum :
      (∑ r : RowKind, 2 * (occupiedRows r S).card) ≤
        ∑ r : RowKind, (rowBoundaryDarts r S).card := by
    exact Finset.sum_le_sum fun r _ =>
      two_mul_occupiedRows_card_le_rowBoundaryDarts_card r S
  rw [sum_rowBoundaryDarts_card] at hsum
  simpa [Finset.mul_sum] using Nat.le_of_mul_le_mul_left hsum

end OeisA263135
