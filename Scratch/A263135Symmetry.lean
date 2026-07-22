import Scratch.A263135CapArithmetic

namespace OeisA263135

/-- Reflection interchanging the first two row directions. -/
def swapVertex (v : Vertex) : Vertex := ⟨v.j, v.i, v.side⟩

@[simp]
theorem swapVertex_involutive (v : Vertex) : swapVertex (swapVertex v) = v := by
  rcases v with ⟨i, j, side⟩
  rfl

theorem swapVertex_injective : Function.Injective swapVertex :=
  Function.LeftInverse.injective swapVertex_involutive

/-- A 120-degree lattice rotation.  On row coordinates it sends
`(first, second, diagonal)` to `(diagonal, first, second)`, up to signs. -/
def rotateVertex : Vertex → Vertex
  | ⟨i, j, false⟩ => ⟨-i - j, i, false⟩
  | ⟨i, j, true⟩ => ⟨-i - j - 1, i, true⟩

theorem rotateVertex_injective : Function.Injective rotateVertex := by
  intro v w h
  rcases v with ⟨i, j, side⟩
  rcases w with ⟨k, l, side'⟩
  cases side <;> cases side' <;> simp [rotateVertex] at h ⊢ <;> omega

/-- Negation of a finite set of integer row labels. -/
def negRows (T : Finset ℤ) : Finset ℤ := T.image fun x => -x

@[simp]
theorem card_negRows (T : Finset ℤ) : (negRows T).card = T.card := by
  exact Finset.card_image_of_injective T neg_injective

@[simp]
theorem rowCoord_swap_first (v : Vertex) :
    rowCoord .first (swapVertex v) = rowCoord .second v := by
  rfl

@[simp]
theorem rowCoord_swap_second (v : Vertex) :
    rowCoord .second (swapVertex v) = rowCoord .first v := by
  rfl

@[simp]
theorem rowCoord_swap_diagonal (v : Vertex) :
    rowCoord .diagonal (swapVertex v) = rowCoord .diagonal v := by
  rcases v with ⟨i, j, side⟩
  cases side <;> simp [swapVertex, rowCoord, add_comm]

@[simp]
theorem rowCoord_rotate_first (v : Vertex) :
    rowCoord .first (rotateVertex v) = -rowCoord .diagonal v := by
  rcases v with ⟨i, j, side⟩
  cases side <;> simp [rotateVertex, rowCoord] <;> ring

@[simp]
theorem rowCoord_rotate_second (v : Vertex) :
    rowCoord .second (rotateVertex v) = rowCoord .first v := by
  rcases v with ⟨i, j, side⟩
  cases side <;> rfl

@[simp]
theorem rowCoord_rotate_diagonal (v : Vertex) :
    rowCoord .diagonal (rotateVertex v) = -rowCoord .second v := by
  rcases v with ⟨i, j, side⟩
  cases side <;> simp [rotateVertex, rowCoord] <;> ring

@[simp]
theorem card_image_swapVertex (S : Finset Vertex) :
    (S.image swapVertex).card = S.card := by
  exact Finset.card_image_of_injective S swapVertex_injective

@[simp]
theorem card_image_rotateVertex (S : Finset Vertex) :
    (S.image rotateVertex).card = S.card := by
  exact Finset.card_image_of_injective S rotateVertex_injective

@[simp]
theorem occupiedRows_swap_first (S : Finset Vertex) :
    occupiedRows .first (S.image swapVertex) = occupiedRows .second S := by
  ext x
  simp [occupiedRows]

@[simp]
theorem occupiedRows_swap_second (S : Finset Vertex) :
    occupiedRows .second (S.image swapVertex) = occupiedRows .first S := by
  ext x
  simp [occupiedRows]

@[simp]
theorem occupiedRows_swap_diagonal (S : Finset Vertex) :
    occupiedRows .diagonal (S.image swapVertex) = occupiedRows .diagonal S := by
  ext x
  simp [occupiedRows]

@[simp]
theorem occupiedRows_rotate_first (S : Finset Vertex) :
    occupiedRows .first (S.image rotateVertex) = negRows (occupiedRows .diagonal S) := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨v, hv, rfl⟩
    rcases Finset.mem_image.mp hv with ⟨w, hw, rfl⟩
    exact Finset.mem_image.mpr
      ⟨rowCoord .diagonal w, Finset.mem_image.mpr ⟨w, hw, rfl⟩, by simp⟩
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨z, hz, rfl⟩
    rcases Finset.mem_image.mp hz with ⟨w, hw, rfl⟩
    exact Finset.mem_image.mpr
      ⟨rotateVertex w, Finset.mem_image.mpr ⟨w, hw, rfl⟩, by simp⟩

@[simp]
theorem occupiedRows_rotate_second (S : Finset Vertex) :
    occupiedRows .second (S.image rotateVertex) = occupiedRows .first S := by
  ext x
  simp [occupiedRows]

@[simp]
theorem occupiedRows_rotate_diagonal (S : Finset Vertex) :
    occupiedRows .diagonal (S.image rotateVertex) = negRows (occupiedRows .second S) := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨v, hv, rfl⟩
    rcases Finset.mem_image.mp hv with ⟨w, hw, rfl⟩
    exact Finset.mem_image.mpr
      ⟨rowCoord .second w, Finset.mem_image.mpr ⟨w, hw, rfl⟩, by simp⟩
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨z, hz, rfl⟩
    rcases Finset.mem_image.mp hz with ⟨w, hw, rfl⟩
    exact Finset.mem_image.mpr
      ⟨rotateVertex w, Finset.mem_image.mpr ⟨w, hw, rfl⟩, by simp⟩

/-- The quadratic row-count inequality, with no ordering assumption. -/
theorem six_mul_card_le_row_sum_sq (S : Finset Vertex) :
    6 * S.card ≤
      ((occupiedRows .first S).card + (occupiedRows .second S).card +
        (occupiedRows .diagonal S).card) ^ 2 := by
  let a := (occupiedRows .first S).card
  let b := (occupiedRows .second S).card
  let c := (occupiedRows .diagonal S).card
  rcases le_total a b with hab | hba
  · rcases le_total b c with hbc | hcb
    · exact six_mul_card_le_row_sum_sq_of_sorted S hab hbc
    · rcases le_total a c with hac | hca
      · have h := six_mul_card_le_row_sum_sq_of_sorted
          ((S.image rotateVertex).image swapVertex) (by simpa [a, c]) (by simpa [b, c])
        simpa [a, b, c, add_assoc, add_left_comm, add_comm] using h
      · have h := six_mul_card_le_row_sum_sq_of_sorted
          (S.image rotateVertex) (by simpa [a, c]) (by simpa [a, b])
        simpa [a, b, c, add_assoc, add_left_comm, add_comm] using h
  · rcases le_total a c with hac | hca
    · have h := six_mul_card_le_row_sum_sq_of_sorted
        (S.image swapVertex) (by simpa [a, b]) (by simpa [a, c])
      simpa [a, b, c, add_assoc, add_left_comm, add_comm] using h
    · rcases le_total b c with hbc | hcb
      · let T := (S.image rotateVertex).image rotateVertex
        have h := six_mul_card_le_row_sum_sq_of_sorted T (by simpa [T, b, c]) (by simpa [T, a, c])
        simpa [T, a, b, c, add_assoc, add_left_comm, add_comm] using h
      · let T := ((S.image rotateVertex).image rotateVertex).image swapVertex
        have h := six_mul_card_le_row_sum_sq_of_sorted T (by simpa [T, b, c]) (by simpa [T, a, b])
        simpa [T, a, b, c, add_assoc, add_left_comm, add_comm] using h

end OeisA263135
