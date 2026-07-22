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

import FormalConjecturesUtil

/-!
# Maximum contacts on the honeycomb lattice

OEIS A263135 is the maximum number of contacts among `m` vertices of the
infinite honeycomb graph.  The conjectured even-index closed form is

`A263135 (2 * n) = 3 * n - ceil (sqrt (3 * n))`.

This file gives a concrete coordinate model of the infinite honeycomb graph
and states that exact extremal theorem.  It also contains the fully proved
integer ceiling arithmetic that turns the closed form into Peter Kagey's OEIS
identity with A047932 and A216256.

*References:*
- [A263135](https://oeis.org/A263135)
- [A047932](https://oeis.org/A047932)
- [A216256](https://oeis.org/A216256)
- Berit Grußien, ["Isoperimetric Inequalities on Hexagonal Grids"](https://arxiv.org/abs/1201.0697)
-/

namespace OeisA263135

/-- The three edge directions incident to a vertex of the honeycomb graph. -/
inductive Direction
  | same
  | horizontal
  | diagonal
  deriving DecidableEq, Fintype

/-- A vertex `A i j` (`side = false`) or `B i j` (`side = true`). -/
structure Vertex where
  i : ℤ
  j : ℤ
  side : Bool
  deriving DecidableEq

/-- The neighbor of `v` in direction `d`.

The coordinate convention is

* `A i j ~ B i j`,
* `A i j ~ B (i - 1) j`,
* `A i j ~ B i (j - 1)`.
-/
def neighbor : Vertex → Direction → Vertex
  | ⟨i, j, false⟩, .same => ⟨i, j, true⟩
  | ⟨i, j, false⟩, .horizontal => ⟨i - 1, j, true⟩
  | ⟨i, j, false⟩, .diagonal => ⟨i, j - 1, true⟩
  | ⟨i, j, true⟩, .same => ⟨i, j, false⟩
  | ⟨i, j, true⟩, .horizontal => ⟨i + 1, j, false⟩
  | ⟨i, j, true⟩, .diagonal => ⟨i, j + 1, false⟩

@[simp]
theorem neighbor_neighbor (v : Vertex) (d : Direction) :
    neighbor (neighbor v d) d = v := by
  rcases v with ⟨i, j, side⟩
  cases side <;> cases d <;> simp [neighbor]

@[simp]
theorem neighbor_ne (v : Vertex) (d : Direction) : neighbor v d ≠ v := by
  rcases v with ⟨i, j, side⟩
  cases side <;> cases d <;> simp [neighbor]

/-- The number of honeycomb edges with both endpoints in `S`.

Every honeycomb edge has exactly one endpoint on the `A` side, so summing the
three neighbor tests only over `A` vertices counts every contact exactly once.
-/
def contacts (S : Finset Vertex) : ℕ :=
  ∑ v in S, if v.side = true then 0 else
    ∑ d : Direction, if neighbor v d ∈ S then 1 else 0

/-- `k` is the maximum contact count among all `N`-vertex honeycomb subsets. -/
def IsMaximumContact (N k : ℕ) : Prop :=
  (∃ S : Finset Vertex, S.card = N ∧ contacts S = k) ∧
    ∀ S : Finset Vertex, S.card = N → contacts S ≤ k

/-- Exact natural-number characterization of `r = ceil (sqrt x)` for positive `x`. -/
def IsNatCeilSqrt (x r : ℕ) : Prop :=
  (r - 1) ^ 2 < x ∧ x ≤ r ^ 2

/-- Integer interval characterizing `ceil (sqrt x)` for positive `x`. -/
def IsCeilSqrt (x r : ℤ) : Prop :=
  0 ≤ r ∧ (r - 1) ^ 2 < x ∧ x ≤ r ^ 2

/-- Integer interval characterizing A216256 at positive index `n`. -/
def IsA216256Index (n k : ℤ) : Prop :=
  0 ≤ k ∧ k ^ 2 - k + 1 < 3 * n ∧ 3 * n ≤ k ^ 2 + k + 1

private lemma isCeilSqrt_unique {x a b : ℤ} (hx : 0 < x)
    (ha : IsCeilSqrt x a) (hb : IsCeilSqrt x b) : a = b := by
  rcases ha with ⟨ha0, haLower, haUpper⟩
  rcases hb with ⟨hb0, hbLower, hbUpper⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hab | hba
  · have hb1 : 1 ≤ b := by
      by_contra h
      have hbzero : b = 0 := by omega
      subst b
      norm_num at hbUpper
      linarith
    have h1 : 0 ≤ b - 1 - a := by omega
    have h2 : 0 ≤ b - 1 + a := by omega
    have hsq : a ^ 2 ≤ (b - 1) ^ 2 := by
      nlinarith [mul_nonneg h1 h2]
    nlinarith
  · have ha1 : 1 ≤ a := by
      by_contra h
      have hazero : a = 0 := by omega
      subst a
      norm_num at haUpper
      linarith
    have h1 : 0 ≤ a - 1 - b := by omega
    have h2 : 0 ≤ a - 1 + b := by omega
    have hsq : b ^ 2 ≤ (a - 1) ^ 2 := by
      nlinarith [mul_nonneg h1 h2]
    nlinarith

/-- The exact ceiling subtraction needed after the honeycomb closed form is known. -/
@[category API, AMS 11]
theorem ceiling_difference
    (n k r s : ℤ)
    (hn : 1 ≤ n)
    (hk : IsA216256Index n k)
    (hr : IsCeilSqrt (3 * n) r)
    (hs : IsCeilSqrt (12 * n - 3) s) :
    s - r = k := by
  rcases hk with ⟨hk0, hkLower, hkUpper⟩
  rcases hr with ⟨hr0, hrLower, hrUpper⟩
  have hk1 : 1 ≤ k := by
    by_contra h
    have hkzero : k = 0 := by omega
    subst k
    norm_num at hkUpper
    nlinarith
  have hk_le_r : k ≤ r := by
    by_contra h
    have hrk : r ≤ k - 1 := by omega
    have h1 : 0 ≤ k - 1 - r := by omega
    have h2 : 0 ≤ k - 1 + r := by omega
    have hsq : r ^ 2 ≤ (k - 1) ^ 2 := by
      nlinarith [mul_nonneg h1 h2]
    nlinarith
  have hr_le : r ≤ k + 1 := by
    by_contra h
    have hkr : k + 2 ≤ r := by omega
    have h1 : 0 ≤ r - 1 - (k + 1) := by omega
    have h2 : 0 ≤ r - 1 + (k + 1) := by omega
    have hsq : (k + 1) ^ 2 ≤ (r - 1) ^ 2 := by
      nlinarith [mul_nonneg h1 h2]
    nlinarith
  rcases (show r = k ∨ r = k + 1 by omega) with hrEq | hrEq
  · subst r
    have hx : 0 < 12 * n - 3 := by nlinarith
    have htarget : IsCeilSqrt (12 * n - 3) (2 * k) := by
      refine ⟨by omega, ?_, ?_⟩ <;> nlinarith
    have hsEq : s = 2 * k := isCeilSqrt_unique hx hs htarget
    omega
  · subst r
    have hrLower' : k ^ 2 < 3 * n := by simpa using hrLower
    have hgap : k ^ 2 + 1 ≤ 3 * n := by omega
    have hx : 0 < 12 * n - 3 := by nlinarith
    have htarget : IsCeilSqrt (12 * n - 3) (2 * k + 1) := by
      refine ⟨by omega, ?_, ?_⟩ <;> nlinarith
    have hsEq : s = 2 * k + 1 := isCeilSqrt_unique hx hs htarget
    omega

/--
**OEIS A263135, stronger even-index form.** For every positive `n`, the maximum
number of contacts among `2 * n` vertices of the infinite honeycomb graph is
`3 * n - ceil (sqrt (3 * n))`.
-/
@[category research open, AMS 05]
theorem conjecture (n : ℕ) (hn : 0 < n) :
    ∃ r : ℕ, IsNatCeilSqrt (3 * n) r ∧
      IsMaximumContact (2 * n) (3 * n - r) := by
  sorry

end OeisA263135
