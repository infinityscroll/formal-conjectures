import Scratch.A263135Ranks

namespace OeisA263135

/-- A ranked honeycomb vertex, forgetting the actual integer row labels. -/
structure RankPoint where
  first : ℕ
  second : ℕ
  side : Bool
  deriving DecidableEq

/-- Embedding of the vertical leg of a rectangle chain. -/
def verticalEmbedding (t : ℕ) (side : Bool) : ℕ ↪ RankPoint where
  toFun j := ⟨t, j, side⟩
  inj' := by
    intro x y h
    exact congrArg RankPoint.second h

/-- Embedding of the horizontal leg of a rectangle chain. -/
def horizontalEmbedding (t b : ℕ) (side : Bool) : ℕ ↪ RankPoint where
  toFun h := ⟨t + 1 + h, b - 1 - t, side⟩
  inj' := by
    intro x y h
    have := congrArg RankPoint.first h
    omega

/-- Vertical part of the `t`-th symmetric chain in an `a × b` rectangle. -/
def verticalChain (b t : ℕ) (side : Bool) : Finset RankPoint :=
  (Finset.range (b - t)).map (verticalEmbedding t side)

/-- Horizontal part after the corner of the `t`-th rectangle chain. -/
def horizontalChain (a b t : ℕ) (side : Bool) : Finset RankPoint :=
  (Finset.range (a - 1 - t)).map (horizontalEmbedding t b side)

/-- The full `t`-th symmetric chain of rectangle cells, on one fixed honeycomb side. -/
def baseBoxChain (a b t : ℕ) (side : Bool) : Finset RankPoint :=
  verticalChain b t side ∪ horizontalChain a b t side

private theorem vertical_horizontal_disjoint (a b t : ℕ) (side : Bool) :
    Disjoint (verticalChain b t side) (horizontalChain a b t side) := by
  rw [Finset.disjoint_left]
  intro p hpv hph
  rcases Finset.mem_map.mp hpv with ⟨j, hj, hjp⟩
  rcases Finset.mem_map.mp hph with ⟨h, hh, hhp⟩
  have heq : (verticalEmbedding t side j).first =
      (horizontalEmbedding t b side h).first := by
    rw [hjp, hhp]
  simp [verticalEmbedding, horizontalEmbedding] at heq
  omega

/-- Cardinality of a base rectangle chain. -/
theorem card_baseBoxChain (a b t : ℕ) (side : Bool)
    (ht : t < a) (hab : a ≤ b) :
    (baseBoxChain a b t side).card = a + b - 1 - 2 * t := by
  rw [baseBoxChain, Finset.card_union_of_disjoint
    (vertical_horizontal_disjoint a b t side)]
  simp [verticalChain, horizontalChain]
  omega

/-- Last rectangle cell of the `t`-th chain. -/
def lastRankPoint (a b t : ℕ) (side : Bool) : RankPoint :=
  ⟨a - 1, b - 1 - t, side⟩

private theorem lastRankPoint_mem_baseBoxChain (a b t : ℕ) (side : Bool)
    (ht : t < a) (hab : a ≤ b) :
    lastRankPoint a b t side ∈ baseBoxChain a b t side := by
  by_cases hlast : t = a - 1
  · apply Finset.mem_union_left
    apply Finset.mem_map.mpr
    refine ⟨b - 1 - t, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · apply RankPoint.ext <;> simp [verticalEmbedding, lastRankPoint, hlast]
  · apply Finset.mem_union_right
    apply Finset.mem_map.mpr
    refine ⟨a - 2 - t, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · apply RankPoint.ext <;> simp [horizontalEmbedding, lastRankPoint]
      omega

/-- Long product chain: every `A` cell of a base chain followed by its final `B` cell. -/
def longBoxChain (a b t : ℕ) : Finset RankPoint :=
  baseBoxChain a b t false ∪ {lastRankPoint a b t true}

/-- Short product chain: every `B` cell except the final cell of the base chain. -/
def shortBoxChain (a b t : ℕ) : Finset RankPoint :=
  (baseBoxChain a b t true).erase (lastRankPoint a b t true)

private theorem base_false_disjoint_last_true (a b t : ℕ) :
    Disjoint (baseBoxChain a b t false) {lastRankPoint a b t true} := by
  rw [Finset.disjoint_singleton_right]
  intro h
  rcases Finset.mem_union.mp h with h | h
  · rcases Finset.mem_map.mp h with ⟨j, hj, heq⟩
    have := congrArg RankPoint.side heq
    simp [verticalEmbedding, lastRankPoint] at this
  · rcases Finset.mem_map.mp h with ⟨k, hk, heq⟩
    have := congrArg RankPoint.side heq
    simp [horizontalEmbedding, lastRankPoint] at this

/-- Length of the long product chain. -/
theorem card_longBoxChain (a b t : ℕ) (ht : t < a) (hab : a ≤ b) :
    (longBoxChain a b t).card = a + b - 2 * t := by
  rw [longBoxChain, Finset.card_union_of_disjoint
    (base_false_disjoint_last_true a b t), card_baseBoxChain _ _ _ _ ht hab]
  simp
  omega

/-- Length of the short product chain. -/
theorem card_shortBoxChain (a b t : ℕ) (ht : t < a) (hab : a ≤ b) :
    (shortBoxChain a b t).card = a + b - 2 - 2 * t := by
  rw [shortBoxChain, Finset.card_erase_of_mem
    (lastRankPoint_mem_baseBoxChain a b t true ht hab),
    card_baseBoxChain _ _ _ _ ht hab]
  omega

end OeisA263135
