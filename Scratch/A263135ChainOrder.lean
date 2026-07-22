import Scratch.A263135ChainMembership

namespace OeisA263135

private theorem baseBoxChain_side {a b t : ℕ} {side : Bool} {p : RankPoint}
    (hp : p ∈ baseBoxChain a b t side) : p.side = side := by
  rcases Finset.mem_union.mp hp with hp | hp
  · rcases Finset.mem_map.mp hp with ⟨j, hj, rfl⟩
    rfl
  · rcases Finset.mem_map.mp hp with ⟨h, hh, rfl⟩
    rfl

/-- Any two points on one base rectangle chain are comparable coordinatewise. -/
theorem baseBoxChain_comparable {a b t : ℕ} {side : Bool} {p q : RankPoint}
    (hp : p ∈ baseBoxChain a b t side)
    (hq : q ∈ baseBoxChain a b t side) :
    (p.first ≤ q.first ∧ p.second ≤ q.second) ∨
      (q.first ≤ p.first ∧ q.second ≤ p.second) := by
  rcases Finset.mem_union.mp hp with hp | hp <;>
    rcases Finset.mem_union.mp hq with hq | hq
  · rcases Finset.mem_map.mp hp with ⟨j, hj, rfl⟩
    rcases Finset.mem_map.mp hq with ⟨k, hk, rfl⟩
    rcases le_total j k with h | h
    · exact Or.inl ⟨le_rfl, h⟩
    · exact Or.inr ⟨le_rfl, h⟩
  · rcases Finset.mem_map.mp hp with ⟨j, hj, rfl⟩
    rcases Finset.mem_map.mp hq with ⟨h, hh, rfl⟩
    left
    simp only [verticalEmbedding, horizontalEmbedding]
    constructor <;> omega
  · rcases Finset.mem_map.mp hp with ⟨h, hh, rfl⟩
    rcases Finset.mem_map.mp hq with ⟨j, hj, rfl⟩
    right
    simp only [verticalEmbedding, horizontalEmbedding]
    constructor <;> omega
  · rcases Finset.mem_map.mp hp with ⟨h, hh, rfl⟩
    rcases Finset.mem_map.mp hq with ⟨k, hk, rfl⟩
    rcases le_total h k with hle | hle
    · exact Or.inl ⟨by omega, le_rfl⟩
    · exact Or.inr ⟨by omega, le_rfl⟩

private theorem baseBoxChain_le_last {a b t : ℕ} {side : Bool} {p : RankPoint}
    (ht : t < a) (hab : a ≤ b)
    (hp : p ∈ baseBoxChain a b t side) :
    p.first ≤ (lastRankPoint a b t side).first ∧
      p.second ≤ (lastRankPoint a b t side).second := by
  rcases Finset.mem_union.mp hp with hp | hp
  · rcases Finset.mem_map.mp hp with ⟨j, hj, rfl⟩
    simp only [verticalEmbedding, lastRankPoint]
    constructor <;> omega
  · rcases Finset.mem_map.mp hp with ⟨h, hh, rfl⟩
    simp only [horizontalEmbedding, lastRankPoint]
    constructor <;> omega

private theorem longBoxChain_true_eq_last {a b t : ℕ} {p : RankPoint}
    (hp : p ∈ longBoxChain a b t) (hside : p.side = true) :
    p = lastRankPoint a b t true := by
  rcases Finset.mem_union.mp hp with hp | hp
  · have := baseBoxChain_side hp
    simp [hside] at this
  · simpa using Finset.mem_singleton.mp hp

private theorem shortBoxChain_side_true {a b t : ℕ} {p : RankPoint}
    (hp : p ∈ shortBoxChain a b t) : p.side = true := by
  exact baseBoxChain_side (Finset.mem_of_mem_erase hp)

private theorem vertex_eq_of_rankPoint_comparable_same_side
    (S : Finset Vertex) (v w : ↥S)
    (hside : v.val.side = w.val.side)
    (hdiag : rowCoord .diagonal v = rowCoord .diagonal w)
    (hcomp :
      ((vertexRankPoint S v).first ≤ (vertexRankPoint S w).first ∧
        (vertexRankPoint S v).second ≤ (vertexRankPoint S w).second) ∨
      ((vertexRankPoint S w).first ≤ (vertexRankPoint S v).first ∧
        (vertexRankPoint S w).second ≤ (vertexRankPoint S v).second)) :
    v = w := by
  have finish
      (hfirst : (vertexRankPoint S v).first ≤ (vertexRankPoint S w).first)
      (hsecond : (vertexRankPoint S v).second ≤ (vertexRankPoint S w).second) : v = w := by
    have hi := rowCoord_le_of_rowRank_le .first S v w hfirst
    have hj := rowCoord_le_of_rowRank_le .second S v w hsecond
    have hieq : rowCoord .first v = rowCoord .first w := by
      rcases v with ⟨⟨iv, jv, sv⟩, hv⟩
      rcases w with ⟨⟨iw, jw, sw⟩, hw⟩
      simp [rowCoord] at hi hj hdiag hside ⊢
      omega
    have hjeq : rowCoord .second v = rowCoord .second w := by
      rcases v with ⟨⟨iv, jv, sv⟩, hv⟩
      rcases w with ⟨⟨iw, jw, sw⟩, hw⟩
      simp [rowCoord] at hi hj hdiag hside ⊢
      omega
    apply Subtype.ext
    apply Vertex.ext
    · simpa [rowCoord] using hieq
    · simpa [rowCoord] using hjeq
    · exact hside
  rcases hcomp with h | h
  · exact finish h.1 h.2
  · exact (finish (v := w) (w := v) hside.symm hdiag.symm h.1 h.2).symm

/-- Third-direction row labels are injective on each long product chain. -/
theorem diagonal_injective_on_longChain
    (S : Finset Vertex) (v w : ↥S)
    (hab : (occupiedRows .first S).card ≤ (occupiedRows .second S).card)
    (ht : vertexChainIndex S v = vertexChainIndex S w)
    (hv : vertexRankPoint S v ∈
      longBoxChain (occupiedRows .first S).card (occupiedRows .second S).card
        (vertexChainIndex S v))
    (hw : vertexRankPoint S w ∈
      longBoxChain (occupiedRows .first S).card (occupiedRows .second S).card
        (vertexChainIndex S w))
    (hdiag : rowCoord .diagonal v = rowCoord .diagonal w) :
    v = w := by
  by_cases hsv : v.val.side = true <;> by_cases hsw : w.val.side = true
  · have hvlast := longBoxChain_true_eq_last hv hsv
    have hwlast := longBoxChain_true_eq_last (ht ▸ hw) hsw
    apply vertexRankPoint_injective S
    rw [hvlast, hwlast]
  · have hvlast := longBoxChain_true_eq_last hv hsv
    have hwbase : vertexRankPoint S w ∈
        baseBoxChain (occupiedRows .first S).card (occupiedRows .second S).card
          (vertexChainIndex S v) false := by
      rcases Finset.mem_union.mp (ht ▸ hw) with h | h
      · exact h
      · have hlast := Finset.mem_singleton.mp h
        have := congrArg RankPoint.side hlast
        simp [hsw, lastRankPoint] at this
    have hle := baseBoxChain_le_last
      (vertexChainIndex_lt_firstRows S v) hab hwbase
    have hi := rowCoord_le_of_rowRank_le .first S w v hle.1
    have hj := rowCoord_le_of_rowRank_le .second S w v hle.2
    rcases v with ⟨⟨iv, jv, sv⟩, hvS⟩
    rcases w with ⟨⟨iw, jw, sw⟩, hwS⟩
    simp [rowCoord] at hi hj hdiag hsv hsw
    omega
  · have hwlast := longBoxChain_true_eq_last (ht ▸ hw) hsw
    have hvbase : vertexRankPoint S v ∈
        baseBoxChain (occupiedRows .first S).card (occupiedRows .second S).card
          (vertexChainIndex S v) false := by
      rcases Finset.mem_union.mp hv with h | h
      · exact h
      · have hlast := Finset.mem_singleton.mp h
        have := congrArg RankPoint.side hlast
        simp [hsv, lastRankPoint] at this
    have hle := baseBoxChain_le_last
      (vertexChainIndex_lt_firstRows S v) hab hvbase
    have hi := rowCoord_le_of_rowRank_le .first S v w hle.1
    have hj := rowCoord_le_of_rowRank_le .second S v w hle.2
    rcases v with ⟨⟨iv, jv, sv⟩, hvS⟩
    rcases w with ⟨⟨iw, jw, sw⟩, hwS⟩
    simp [rowCoord] at hi hj hdiag hsv hsw
    omega
  · have hcomp := baseBoxChain_comparable
      (show vertexRankPoint S v ∈
        baseBoxChain (occupiedRows .first S).card (occupiedRows .second S).card
          (vertexChainIndex S v) false by
        rcases Finset.mem_union.mp hv with h | h
        · exact h
        · have hlast := Finset.mem_singleton.mp h
          have := congrArg RankPoint.side hlast
          simp [hsv, lastRankPoint] at this)
      (show vertexRankPoint S w ∈
        baseBoxChain (occupiedRows .first S).card (occupiedRows .second S).card
          (vertexChainIndex S v) false by
        rcases Finset.mem_union.mp (ht ▸ hw) with h | h
        · exact h
        · have hlast := Finset.mem_singleton.mp h
          have := congrArg RankPoint.side hlast
          simp [hsw, lastRankPoint] at this)
    exact vertex_eq_of_rankPoint_comparable_same_side S v w
      (Bool.eq_false_of_not_eq_true hsv |>.trans
        (Bool.eq_false_of_not_eq_true hsw).symm) hdiag hcomp

/-- Third-direction row labels are injective on each short product chain. -/
theorem diagonal_injective_on_shortChain
    (S : Finset Vertex) (v w : ↥S)
    (ht : vertexChainIndex S v = vertexChainIndex S w)
    (hv : vertexRankPoint S v ∈
      shortBoxChain (occupiedRows .first S).card (occupiedRows .second S).card
        (vertexChainIndex S v))
    (hw : vertexRankPoint S w ∈
      shortBoxChain (occupiedRows .first S).card (occupiedRows .second S).card
        (vertexChainIndex S w))
    (hdiag : rowCoord .diagonal v = rowCoord .diagonal w) :
    v = w := by
  have hcomp := baseBoxChain_comparable
    (Finset.mem_of_mem_erase hv)
    (Finset.mem_of_mem_erase (ht ▸ hw))
  exact vertex_eq_of_rankPoint_comparable_same_side S v w
    ((shortBoxChain_side_true hv).trans (shortBoxChain_side_true (ht ▸ hw)).symm)
    hdiag hcomp

end OeisA263135
