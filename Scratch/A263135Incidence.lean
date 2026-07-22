import Scratch.A263135Symmetry

namespace OeisA263135

/-- Directed honeycomb incidences whose two endpoints lie in `S`. -/
def internalDarts (S : Finset Vertex) : Finset (Vertex × Direction) :=
  (S ×ˢ Finset.univ).filter fun vd => neighbor vd.1 vd.2 ∈ S

/-- Internal darts based at the `A` side. -/
def aInternalDarts (S : Finset Vertex) : Finset (Vertex × Direction) :=
  (internalDarts S).filter fun vd => vd.1.side = false

/-- Internal darts based at the `B` side. -/
def bInternalDarts (S : Finset Vertex) : Finset (Vertex × Direction) :=
  (internalDarts S).filter fun vd => vd.1.side = true

private theorem internal_boundary_disjoint (S : Finset Vertex) :
    Disjoint (internalDarts S) (boundaryDarts S) := by
  rw [Finset.disjoint_left]
  intro vd hi hb
  exact (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hb).2

private theorem internal_union_boundary (S : Finset Vertex) :
    internalDarts S ∪ boundaryDarts S = S ×ˢ Finset.univ := by
  ext vd
  simp [internalDarts, boundaryDarts]

/-- Every vertex has three directed incidences, split into internal and boundary darts. -/
theorem card_internalDarts_add_edgeBoundary (S : Finset Vertex) :
    (internalDarts S).card + edgeBoundary S = 3 * S.card := by
  rw [edgeBoundary, ← Finset.card_union_of_disjoint (internal_boundary_disjoint S),
    internal_union_boundary]
  simp [mul_comm]

private theorem a_b_internal_disjoint (S : Finset Vertex) :
    Disjoint (aInternalDarts S) (bInternalDarts S) := by
  rw [Finset.disjoint_left]
  intro vd ha hb
  have hfalse := (Finset.mem_filter.mp ha).2
  have htrue := (Finset.mem_filter.mp hb).2
  simp [hfalse] at htrue

private theorem a_union_b_internal (S : Finset Vertex) :
    aInternalDarts S ∪ bInternalDarts S = internalDarts S := by
  ext vd
  simp [aInternalDarts, bInternalDarts]
  cases h : vd.1.side <;> simp [h]

/-- Reversal of a directed honeycomb incidence. -/
def reverseDart (vd : Vertex × Direction) : Vertex × Direction :=
  (neighbor vd.1 vd.2, vd.2)

@[simp]
theorem reverseDart_involutive (vd : Vertex × Direction) :
    reverseDart (reverseDart vd) = vd := by
  rcases vd with ⟨v, d⟩
  simp [reverseDart]

private theorem reverseDart_injective : Function.Injective reverseDart :=
  Function.LeftInverse.injective reverseDart_involutive

private theorem reverse_a_mem_b (S : Finset Vertex) {vd : Vertex × Direction}
    (h : vd ∈ aInternalDarts S) : reverseDart vd ∈ bInternalDarts S := by
  rcases vd with ⟨v, d⟩
  rcases Finset.mem_filter.mp h with ⟨hint, hvside⟩
  rcases Finset.mem_filter.mp hint with ⟨hprod, hnmem⟩
  rcases Finset.mem_product.mp hprod with ⟨hvS, hd⟩
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨hnmem, hd⟩, by simpa⟩
  · rcases v with ⟨i, j, side⟩
    cases side <;> cases d <;> simp [reverseDart, neighbor] at hvside ⊢

private theorem reverse_b_mem_a (S : Finset Vertex) {vd : Vertex × Direction}
    (h : vd ∈ bInternalDarts S) : reverseDart vd ∈ aInternalDarts S := by
  rcases vd with ⟨v, d⟩
  rcases Finset.mem_filter.mp h with ⟨hint, hvside⟩
  rcases Finset.mem_filter.mp hint with ⟨hprod, hnmem⟩
  rcases Finset.mem_product.mp hprod with ⟨hvS, hd⟩
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨hnmem, hd⟩, by simpa⟩
  · rcases v with ⟨i, j, side⟩
    cases side <;> cases d <;> simp [reverseDart, neighbor] at hvside ⊢

/-- Internal darts based at the two bipartite sides are equinumerous. -/
theorem card_aInternalDarts_eq_card_bInternalDarts (S : Finset Vertex) :
    (aInternalDarts S).card = (bInternalDarts S).card := by
  apply Nat.le_antisymm
  · exact Finset.card_le_card_of_injOn reverseDart
      (fun _ h => reverse_a_mem_b S h)
      (fun _ _ _ _ h => reverseDart_injective h)
  · exact Finset.card_le_card_of_injOn reverseDart
      (fun _ h => reverse_b_mem_a S h)
      (fun _ _ _ _ h => reverseDart_injective h)

/-- The original `contacts` sum is the cardinality of the `A`-based internal darts. -/
theorem contacts_eq_card_aInternalDarts (S : Finset Vertex) :
    contacts S = (aInternalDarts S).card := by
  classical
  unfold contacts aInternalDarts internalDarts
  rw [Finset.card_eq_sum_card_fiberwise
    (s := ((S ×ˢ Finset.univ).filter fun vd => neighbor vd.1 vd.2 ∈ S).filter
      fun vd => vd.1.side = false)
    (g := Prod.fst) (t := S) (by simp)]
  apply Finset.sum_congr rfl
  intro v hv
  cases hside : v.side
  · simp [hside]
  · simp [hside, Finset.card_eq_sum_ones]

/-- The number of directed internal darts is twice the contact count. -/
theorem card_internalDarts_eq_two_mul_contacts (S : Finset Vertex) :
    (internalDarts S).card = 2 * contacts S := by
  rw [← a_union_b_internal S,
    Finset.card_union_of_disjoint (a_b_internal_disjoint S),
    ← contacts_eq_card_aInternalDarts,
    ← card_aInternalDarts_eq_card_bInternalDarts S]
  omega

/-- Incidence bookkeeping for every finite honeycomb set. -/
theorem three_mul_card_eq_two_mul_contacts_add_boundary (S : Finset Vertex) :
    3 * S.card = 2 * contacts S + edgeBoundary S := by
  rw [← card_internalDarts_eq_two_mul_contacts]
  omega

end OeisA263135
