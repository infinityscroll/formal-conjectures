import Scratch.A263135BoxChains

namespace OeisA263135

/-- Pair of the first two occupied-row ranks. -/
noncomputable def rectangleRankPair (S : Finset Vertex) (v : ↥S) :
    Fin (occupiedRows .first S).card × Fin (occupiedRows .second S).card :=
  (rowRank .first S v, rowRank .second S v)

/-- Ranked point corresponding to a honeycomb vertex. -/
noncomputable def vertexRankPoint (S : Finset Vertex) (v : ↥S) : RankPoint :=
  ⟨(rowRank .first S v).val, (rowRank .second S v).val, v.val.side⟩

/-- Rectangle-chain index of a honeycomb vertex. -/
noncomputable def vertexChainIndex (S : Finset Vertex) (v : ↥S) : ℕ :=
  rectangleChainIndex (rectangleRankPair S v)

/-- Product-chain choice of a honeycomb vertex. -/
noncomputable def vertexSubchain (S : Finset Vertex) (v : ↥S) : Bool :=
  boxSubchain (rectangleRankPair S v) v.val.side

/-- A vertex's rectangle-chain index lies in the first-row range. -/
theorem vertexChainIndex_lt_firstRows (S : Finset Vertex) (v : ↥S) :
    vertexChainIndex S v < (occupiedRows .first S).card := by
  unfold vertexChainIndex rectangleChainIndex rectangleRankPair
  exact lt_of_le_of_lt (Nat.min_le_left _ _) (rowRank .first S v).isLt

private theorem rankPoint_mem_baseBoxChain (S : Finset Vertex) (v : ↥S)
    (hab : (occupiedRows .first S).card ≤ (occupiedRows .second S).card) :
    vertexRankPoint S v ∈
      baseBoxChain (occupiedRows .first S).card (occupiedRows .second S).card
        (vertexChainIndex S v) v.val.side := by
  let a := (occupiedRows .first S).card
  let b := (occupiedRows .second S).card
  let p := rectangleRankPair S v
  let t := vertexChainIndex S v
  have hi : p.1.val < a := p.1.isLt
  have hj : p.2.val < b := p.2.isLt
  have ht : t = min p.1.val (b - 1 - p.2.val) := rfl
  by_cases hvertical : p.1.val ≤ b - 1 - p.2.val
  · apply Finset.mem_union_left
    apply Finset.mem_map.mpr
    refine ⟨p.2.val, ?_, ?_⟩
    · simp only [Finset.mem_range]
      rw [ht, Nat.min_eq_left hvertical]
      omega
    · apply RankPoint.ext <;>
        simp [vertexRankPoint, rectangleRankPair, verticalEmbedding, t, p, ht,
          Nat.min_eq_left hvertical]
  · apply Finset.mem_union_right
    apply Finset.mem_map.mpr
    let h := p.1.val - (t + 1)
    refine ⟨h, ?_, ?_⟩
    · simp only [Finset.mem_range]
      rw [ht, Nat.min_eq_right (Nat.le_of_not_ge hvertical)] at *
      dsimp [h]
      omega
    · apply RankPoint.ext <;>
        simp [vertexRankPoint, rectangleRankPair, horizontalEmbedding, t, p, h, ht,
          Nat.min_eq_right (Nat.le_of_not_ge hvertical)]
      omega

private theorem vertexRankPoint_last_iff (S : Finset Vertex) (v : ↥S) :
    vertexRankPoint S v =
        lastRankPoint (occupiedRows .first S).card (occupiedRows .second S).card
          (vertexChainIndex S v) v.val.side ↔
      isRectangleChainLast (rectangleRankPair S v) := by
  constructor
  · intro h
    constructor
    · exact congrArg RankPoint.first h
    · exact congrArg RankPoint.second h
  · rintro ⟨hi, hj⟩
    apply RankPoint.ext <;>
      simp [vertexRankPoint, lastRankPoint, rectangleRankPair, hi, hj]

/-- Every ranked vertex belongs to its chosen long or short product chain. -/
theorem vertexRankPoint_mem_chosenChain (S : Finset Vertex) (v : ↥S)
    (hab : (occupiedRows .first S).card ≤ (occupiedRows .second S).card) :
    if vertexSubchain S v then
      vertexRankPoint S v ∈
        shortBoxChain (occupiedRows .first S).card (occupiedRows .second S).card
          (vertexChainIndex S v)
    else
      vertexRankPoint S v ∈
        longBoxChain (occupiedRows .first S).card (occupiedRows .second S).card
          (vertexChainIndex S v) := by
  have hbase := rankPoint_mem_baseBoxChain S v hab
  unfold vertexSubchain boxSubchain
  by_cases hside : v.val.side = true
  · simp only [hside, Bool.true_and, Bool.decide_coe]
    by_cases hlast : isRectangleChainLast (rectangleRankPair S v)
    · simp [hlast, longBoxChain, vertexRankPoint_last_iff.mpr hlast]
    · simp [hlast, shortBoxChain, hbase, vertexRankPoint_last_iff, hlast]
  · have hfalse : v.val.side = false := Bool.eq_false_of_not_eq_true hside
    simp [hfalse, longBoxChain, hbase]

/-- The ranked-point map is injective. -/
theorem vertexRankPoint_injective (S : Finset Vertex) :
    Function.Injective (vertexRankPoint S) := by
  intro v w h
  have hfirst : rowRank .first S v = rowRank .first S w := by
    apply Fin.ext
    exact congrArg RankPoint.first h
  have hsecond : rowRank .second S v = rowRank .second S w := by
    apply Fin.ext
    exact congrArg RankPoint.second h
  have hside : v.val.side = w.val.side := congrArg RankPoint.side h
  apply Subtype.ext
  apply Vertex.ext
  · simpa [rowCoord] using (rowRank_eq_iff_rowCoord_eq .first S v w).mp hfirst
  · simpa [rowCoord] using (rowRank_eq_iff_rowCoord_eq .second S v w).mp hsecond
  · exact hside

end OeisA263135
