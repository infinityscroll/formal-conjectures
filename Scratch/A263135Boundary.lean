import Scratch.A263135Rows

namespace OeisA263135

/-- Row directions preserved by a directed honeycomb edge. -/
def preservedRows (vd : Vertex × Direction) : Finset RowKind :=
  Finset.univ.filter fun r => rowCoord r (neighbor vd.1 vd.2) = rowCoord r vd.1

@[simp]
theorem card_preservedRows (v : Vertex) (d : Direction) :
    (preservedRows (v, d)).card = 2 := by
  rcases v with ⟨i, j, side⟩
  cases side <;> cases d <;>
    simp [preservedRows, rowCoord, neighbor]

/-- Boundary darts lying along the rows of kind `r`. -/
def rowBoundaryDarts (r : RowKind) (S : Finset Vertex) : Finset (Vertex × Direction) :=
  (boundaryDarts S).filter fun vd => r ∈ preservedRows vd

/-- Every boundary dart is counted in exactly two of the three row families. -/
theorem sum_rowBoundaryDarts_card (S : Finset Vertex) :
    (∑ r : RowKind, (rowBoundaryDarts r S).card) = 2 * edgeBoundary S := by
  classical
  simp_rw [rowBoundaryDarts, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp only [edgeBoundary]
  calc
    (∑ vd ∈ boundaryDarts S, ∑ r : RowKind, if r ∈ preservedRows vd then 1 else 0) =
        ∑ vd ∈ boundaryDarts S, (preservedRows vd).card := by
          apply Finset.sum_congr rfl
          intro vd hv
          simp [Finset.card_eq_sum_ones]
    _ = ∑ _vd ∈ boundaryDarts S, 2 := by
          apply Finset.sum_congr rfl
          intro vd hv
          rcases vd with ⟨v, d⟩
          simp
    _ = 2 * (boundaryDarts S).card := by simp [mul_comm]

end OeisA263135
