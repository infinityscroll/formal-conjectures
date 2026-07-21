/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import FormalConjectures.WrittenOnTheWallII.GraphConjecture200

/-!
# A counterexample to Written on the Wall II, Graph Conjecture 200

This file is intentionally standalone: it imports the current upstream
formalization but does not modify it.  The concrete graph has graph6 encoding
`J??FFBRq}N_`.
-/

namespace WOWII200Counterexample

open SimpleGraph

/-- The smallest counterexample found by exhaustive unlabeled-graph search.

The vertices `6,7,8,9,10` induce `K₅` minus the edge `6-7`; vertices `0,1`
are adjacent to all five core vertices; `2` is adjacent to `6,7`; and
`3,4,5` are pendant at `8,9,10`, respectively. -/
def edgeFinsetG : Finset (Sym2 (Fin 11)) :=
  {
    s(0, 6), s(1, 6), s(2, 6),
    s(0, 7), s(1, 7), s(2, 7),
    s(0, 8), s(1, 8), s(3, 8), s(6, 8), s(7, 8),
    s(0, 9), s(1, 9), s(4, 9), s(6, 9), s(7, 9), s(8, 9),
    s(0, 10), s(1, 10), s(5, 10), s(6, 10), s(7, 10), s(8, 10), s(9, 10)
  }

abbrev G : SimpleGraph (Fin 11) :=
  SimpleGraph.fromEdgeSet (edgeFinsetG : Set (Sym2 (Fin 11)))

instance instDecidableGAdj : DecidableRel G.Adj := by
  infer_instance

/-- A decidable characterization of an induced tree: connected, with one
fewer edge than vertex. -/
def computableIsInducedTree {α : Type*} [Fintype α] [DecidableEq α]
    (H : SimpleGraph α) [DecidableRel H.Adj] (s : Finset α) : Prop :=
  let K := H.induce (s : Set α)
  K.Connected ∧ K.edgeFinset.card + 1 = Fintype.card ↥(s : Set α)

instance instDecidableComputableIsInducedTree
    {α : Type*} [Fintype α] [DecidableEq α]
    (H : SimpleGraph α) [DecidableRel H.Adj] (s : Finset α) :
    Decidable (computableIsInducedTree H s) := by
  unfold computableIsInducedTree
  infer_instance

theorem computableIsInducedTree_iff {α : Type*} [Fintype α] [DecidableEq α]
    (H : SimpleGraph α) [DecidableRel H.Adj] (s : Finset α) :
    computableIsInducedTree H s ↔ (H.induce (s : Set α)).IsTree := by
  rw [isTree_iff_connected_and_card]
  constructor
  · rintro ⟨hc, he⟩
    refine ⟨hc, ?_⟩
    simpa only [Nat.card_eq_fintype_card, ← edgeFinset_card] using he
  · rintro ⟨hc, he⟩
    refine ⟨hc, ?_⟩
    simpa only [Nat.card_eq_fintype_card, ← edgeFinset_card] using he

/-- Powerset-enumeration version of `largestInducedTreeSize`. -/
def computableLargestInducedTreeSize {α : Type*} [Fintype α] [DecidableEq α]
    (H : SimpleGraph α) [DecidableRel H.Adj] : ℕ :=
  (Finset.univ.powerset.filter fun s : Finset α =>
    computableIsInducedTree H s).sup Finset.card

/-- The computable finite maximum agrees with the `sSup` definition used by
Formal Conjectures. -/
theorem largestInducedTreeSize_eq_computable
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (H : SimpleGraph α) [DecidableRel H.Adj] :
    largestInducedTreeSize H = computableLargestInducedTreeSize H := by
  unfold largestInducedTreeSize computableLargestInducedTreeSize
  apply le_antisymm
  · apply csSup_le
    · let v : α := Classical.choice inferInstance
      refine ⟨1, {v}, by simp, ?_⟩
      letI : Nonempty {x : α // x ∈ (↑({v} : Finset α) : Set α)} :=
        ⟨⟨v, by simp⟩⟩
      letI : Subsingleton {x : α // x ∈ (↑({v} : Finset α) : Set α)} :=
        ⟨by
          rintro ⟨x, hx⟩ ⟨y, hy⟩
          apply Subtype.ext
          have hxv : x = v := by simpa using hx
          have hyv : y = v := by simpa using hy
          exact hxv.trans hyv.symm⟩
      exact IsTree.of_subsingleton
    · rintro n ⟨s, hcard, htree⟩
      rw [← hcard]
      apply Finset.le_sup
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr (Finset.subset_univ s),
          (computableIsInducedTree_iff H s).mpr htree⟩
  · apply Finset.sup_le
    intro s hs
    apply le_csSup
    · exact ⟨Fintype.card α, fun n ⟨t, ht, _⟩ => ht ▸ t.card_le_univ⟩
    · exact ⟨s, rfl, (computableIsInducedTree_iff H s).mp (Finset.mem_filter.mp hs).2⟩

/-- The graph is connected. -/
theorem connected : G.Connected := by
  decide +native

theorem neighborSet_three : G.neighborSet (3 : Fin 11) = {(8 : Fin 11)} := by
  ext v
  fin_cases v <;> decide

theorem neighborSet_four : G.neighborSet (4 : Fin 11) = {(9 : Fin 11)} := by
  ext v
  fin_cases v <;> decide

theorem neighborSet_five : G.neighborSet (5 : Fin 11) = {(10 : Fin 11)} := by
  ext v
  fin_cases v <;> decide

/-- Exact local-neighborhood independence-number sum. -/
theorem localIndependenceSum :
    (∑ v : Fin 11, indepNeighborsCard G v) = 24 := by
  simp_rw [indepNeighborsCard, indep_num_eq_computable]
  decide +native

/-- The exact average local independence number is `24/11`. -/
theorem averageLocalIndependence : averageIndepNeighbors G = 24 / 11 := by
  unfold averageIndepNeighbors indepNeighbors
  change (∑ v : Fin 11, (indepNeighborsCard G v : ℝ)) / 11 = 24 / 11
  rw [← Nat.cast_sum, localIndependenceSum]
  norm_num

/-- The largest induced tree has four vertices.  The lower witness is the
induced claw on `{0,1,2,6}`; the upper bound is an exhaustive finite decision
over all `2^11` vertex subsets. -/
theorem largestInducedTreeSize_eq_four : largestInducedTreeSize G = 4 := by
  rw [largestInducedTreeSize_eq_computable]
  decide +native

/-- The numerical premise of Conjecture 200 holds exactly. -/
theorem conjecturePremise :
    (largestInducedTreeSize G : ℝ) = ⌈1 + averageIndepNeighbors G⌉ := by
  rw [largestInducedTreeSize_eq_four, averageLocalIndependence]
  norm_num

/-- Every leaf appearing in a Hamiltonian path must be one of its two
endpoints.  Our graph has the three distinct leaves `3,4,5`, so it has no
Hamiltonian path. -/
theorem noHamiltonianPath :
    ¬ ∃ a b : Fin 11, ∃ p : G.Walk a b, p.IsHamiltonian := by
  rintro ⟨a, b, p, hp⟩
  have leaf_is_endpoint (v : Fin 11) (hv : (G.neighborSet v).Subsingleton) :
      v = a ∨ v = b := by
    by_contra h
    push_neg at h
    exact (hp.isPath.isTrail.not_mem_support_of_subsingleton_neighborSet h.1 h.2 hv)
      (hp.mem_support v)
  have h3 : (3 : Fin 11) = a ∨ (3 : Fin 11) = b := by
    apply leaf_is_endpoint
    rw [neighborSet_three]
    exact Set.subsingleton_singleton
  have h4 : (4 : Fin 11) = a ∨ (4 : Fin 11) = b := by
    apply leaf_is_endpoint
    rw [neighborSet_four]
    exact Set.subsingleton_singleton
  have h5 : (5 : Fin 11) = a ∨ (5 : Fin 11) = b := by
    apply leaf_is_endpoint
    rw [neighborSet_five]
    exact Set.subsingleton_singleton
  rcases h3 with h3 | h3 <;>
    rcases h4 with h4 | h4 <;>
    rcases h5 with h5 | h5 <;>
    omega

/-- The exact current Formal Conjectures statement is false. -/
theorem conjecture200_false :
    ¬ (∀ (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α]
      (H : SimpleGraph α) (_h : H.Connected),
      (largestInducedTreeSize H : ℝ) = ⌈1 + averageIndepNeighbors H⌉ →
      ∃ a b : α, ∃ p : H.Walk a b, p.IsHamiltonian) := by
  intro h
  exact noHamiltonianPath (h (Fin 11) G connected conjecturePremise)

end WOWII200Counterexample

