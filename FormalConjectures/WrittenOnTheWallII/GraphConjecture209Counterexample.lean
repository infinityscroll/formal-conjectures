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
import FormalConjectures.WrittenOnTheWallII.GraphConjecture209

/-!
# A counterexample to Written on the Wall II, Graph Conjecture 209

This file is intentionally standalone: it imports the upstream formalization
but does not modify it. The concrete graph has graph6 encoding `J?o}]^Nr}^_`
(canonical labeling); here we use the transparent labeling below.
-/

namespace WOWII209Counterexample

open SimpleGraph
open WrittenOnTheWallII.GraphConjecture209

/-- The smallest counterexample, found by exhaustive unlabeled-graph search.

Vertices `0,…,6` induce `K₇`; vertices `7` and `8` are nonadjacent and each
adjacent to `1,…,6` (all of the clique except `0`); vertices `9` and `10` are
pendant, both adjacent exactly to `0`. -/
def edgeFinsetG : Finset (Sym2 (Fin 11)) :=
  {
    s(0, 1), s(0, 2), s(0, 3), s(0, 4), s(0, 5), s(0, 6),
    s(1, 2), s(1, 3), s(1, 4), s(1, 5), s(1, 6),
    s(2, 3), s(2, 4), s(2, 5), s(2, 6),
    s(3, 4), s(3, 5), s(3, 6),
    s(4, 5), s(4, 6),
    s(5, 6),
    s(1, 7), s(2, 7), s(3, 7), s(4, 7), s(5, 7), s(6, 7),
    s(1, 8), s(2, 8), s(3, 8), s(4, 8), s(5, 8), s(6, 8),
    s(0, 9), s(0, 10)
  }

abbrev G : SimpleGraph (Fin 11) :=
  SimpleGraph.fromEdgeSet (edgeFinsetG : Set (Sym2 (Fin 11)))

instance instDecidableGAdj : DecidableRel G.Adj := by
  infer_instance

/-- The graph is connected. -/
theorem connected : G.Connected := by
  decide +native

/-- The maximum local independence number is `3`. -/
theorem lambdaMax_eq : lambdaMax G = 3 := by
  unfold lambdaMax
  simp_rw [indepNeighborsCard, indep_num_eq_computable]
  decide +native

/-- Exactly the seven clique vertices attain the maximum. -/
theorem lambdaMaxFreq_eq : lambdaMaxFreq G = 7 := by
  unfold lambdaMaxFreq lambdaMax
  simp_rw [indepNeighborsCard, indep_num_eq_computable]
  decide +native

/-- The complement has `20` edges. -/
theorem card_edgeFinset_compl : (Gᶜ).edgeFinset.card = 20 := by
  decide +native

/-- The numerical premise of Conjecture 209 holds:
`(1/6)(1 + 2·20) = 41/6 ≤ 7`. -/
theorem conjecturePremise :
    (1 : ℝ) / 6 * (1 + 2 * ((Gᶜ).edgeFinset.card : ℝ)) ≤ lambdaMaxFreq G := by
  rw [card_edgeFinset_compl, lambdaMaxFreq_eq]
  norm_num

theorem neighborSet_nine : G.neighborSet (9 : Fin 11) = {(0 : Fin 11)} := by
  ext v
  fin_cases v <;> decide

theorem neighborSet_ten : G.neighborSet (10 : Fin 11) = {(0 : Fin 11)} := by
  ext v
  fin_cases v <;> decide

/-- No Hamiltonian path can join two pendant vertices that share their unique
neighbour: the second and penultimate vertices of the path would coincide,
forcing the path to have length `2`, impossible on `11` vertices. -/
theorem no_ham_between_pendants {u v : Fin 11}
    (hu : G.neighborSet u = {(0 : Fin 11)})
    (hv : G.neighborSet v = {(0 : Fin 11)})
    (p : G.Walk u v) (hp : p.IsHamiltonian) : False := by
  have hlen : p.length = 10 := by
    have h := hp.length_eq
    norm_num [Fintype.card_fin] at h
    exact h
  have hnil : ¬ p.Nil := by
    rw [Walk.not_nil_iff_lt_length, hlen]
    norm_num
  have hsnd : p.snd = 0 := by
    have h : p.snd ∈ G.neighborSet u := Walk.adj_snd hnil
    rw [hu] at h
    simpa using h
  have hpen : p.penultimate = 0 := by
    have h : p.penultimate ∈ G.neighborSet v := (Walk.adj_penultimate hnil).symm
    rw [hv] at h
    simpa using h
  have hinj := hp.isPath.getVert_injOn
  have h19 : (1 : ℕ) = p.length - 1 := by
    apply hinj
    · rw [Set.mem_setOf_eq, hlen]; omega
    · rw [Set.mem_setOf_eq]; omega
    · exact hsnd.trans hpen.symm
  rw [hlen] at h19
  omega

/-- Every leaf of a Hamiltonian path is one of its two endpoints; our two
pendant vertices `9` and `10` both attach to vertex `0`, so the graph has no
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
  have h9 : (9 : Fin 11) = a ∨ (9 : Fin 11) = b := by
    apply leaf_is_endpoint
    rw [neighborSet_nine]
    exact Set.subsingleton_singleton
  have h10 : (10 : Fin 11) = a ∨ (10 : Fin 11) = b := by
    apply leaf_is_endpoint
    rw [neighborSet_ten]
    exact Set.subsingleton_singleton
  rcases h9 with h9 | h9 <;> rcases h10 with h10 | h10
  · exact absurd (h9.trans h10.symm) (by decide)
  · subst h9; subst h10
    exact no_ham_between_pendants neighborSet_nine neighborSet_ten p hp
  · subst h9; subst h10
    exact no_ham_between_pendants neighborSet_ten neighborSet_nine p hp
  · exact absurd (h9.trans h10.symm) (by decide)

/-- The exact Formal Conjectures statement of Conjecture 209 is false. -/
theorem conjecture209_false :
    ¬ (∀ (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α]
      (H : SimpleGraph α) [DecidableRel H.Adj] (_h : H.Connected),
      (1 : ℝ) / 6 * (1 + 2 * ((Hᶜ).edgeFinset.card : ℝ)) ≤ lambdaMaxFreq H →
      ∃ a b : α, ∃ p : H.Walk a b, p.IsHamiltonian) := by
  intro h
  exact noHamiltonianPath (h (Fin 11) G connected conjecturePremise)

end WOWII209Counterexample
