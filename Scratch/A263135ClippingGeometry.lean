import Scratch.A263135ClippingDarts

namespace OeisA263135

/-- Ranked B endpoint of a ranked A-based dart. -/
def rankDartNeighbor : RankPoint × Direction → RankPoint
  | (p, .same) => sameRankNeighbor p
  | (p, .horizontal) => horizontalRankNeighbor p
  | (p, .diagonal) => diagonalRankNeighbor p

@[simp]
theorem clipBPoint_side (a b k : ℕ) : (clipBPoint a b k).side = true := by
  unfold clipBPoint
  split_ifs <;> rfl

@[simp]
theorem clipAPoint_side (a b k : ℕ) : (clipAPoint a b k).side = false := by
  unfold clipAPoint
  split_ifs <;> rfl

@[simp]
theorem clipForwardAPoint_side (a b k : ℕ) :
    (clipForwardAPoint a b k).side = false := by
  unfold clipForwardAPoint
  split_ifs <;> rfl

@[simp]
theorem rankDartNeighbor_side (pd : RankPoint × Direction) :
    (rankDartNeighbor pd).side = true := by
  rcases pd with ⟨p, d⟩
  cases d <;> rfl

@[simp]
theorem rankDartNeighbor_clipA_diagonal (a b k : ℕ) :
    rankDartNeighbor (clipAPoint a b k, .diagonal) = clipBPoint a b k := by
  by_cases hkb : k < b
  · apply RankPoint.ext <;>
      simp [rankDartNeighbor, diagonalRankNeighbor, clipAPoint, clipBPoint, hkb] <;> omega
  · apply RankPoint.ext <;>
      simp [rankDartNeighbor, diagonalRankNeighbor, clipAPoint, clipBPoint, hkb] <;> omega

@[simp]
theorem rankDartNeighbor_clipForward_horizontal (a b k : ℕ) :
    rankDartNeighbor (clipForwardAPoint a b k, .horizontal) = clipBPoint a b k := by
  by_cases hkb : k < b
  · apply RankPoint.ext <;>
      simp [rankDartNeighbor, horizontalRankNeighbor, clipForwardAPoint, clipBPoint, hkb] <;> omega
  · apply RankPoint.ext <;>
      simp [rankDartNeighbor, horizontalRankNeighbor, clipForwardAPoint, clipBPoint, hkb] <;> omega

/-- Membership in the union of the first `d` clipping pairs. -/
theorem mem_clippedRankPoints_iff {a b d : ℕ} {p : RankPoint} :
    p ∈ clippedRankPoints a b d ↔
      ∃ k < d, p = clipBPoint a b k ∨ p = clipAPoint a b k := by
  constructor
  · intro hp
    rcases Finset.mem_biUnion.mp hp with ⟨k, hk, hpk⟩
    have hk' : k < d := Finset.mem_range.mp hk
    rw [clipPair_eq] at hpk
    simpa only [Finset.mem_insert, Finset.mem_singleton] using ⟨k, hk', hpk⟩
  · rintro ⟨k, hk, hpk⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨k, Finset.mem_range.mpr hk, ?_⟩
    rw [clipPair_eq]
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hpk

private theorem clipAPoint_mem_aRankPatch
    (a b c k : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a ≤ b) (hk : k < a + b - 1) :
    clipAPoint a b k ∈ aRankPatch a b c := by
  apply Finset.mem_filter.mpr
  constructor
  · rw [mem_rankPatch]
    by_cases hkb : k < b <;>
      simp [clipAPoint, rankLevel, hkb] <;> omega
  · exact clipAPoint_side a b k

private theorem clipForwardAPoint_mem_aRankPatch
    (a b c k : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a ≤ b) (hk : k < a + b - 1) :
    clipForwardAPoint a b k ∈ aRankPatch a b c := by
  apply Finset.mem_filter.mpr
  constructor
  · rw [mem_rankPatch]
    by_cases hkb : k < b <;>
      simp [clipForwardAPoint, rankLevel, hkb] <;> omega
  · exact clipForwardAPoint_side a b k

private theorem clipAPoint_rankLevel_ne_top
    (a b c k : ℕ) (ha : 0 < a) (hc : 0 < c)
    (hk : k < a + b - 1) :
    rankLevel (clipAPoint a b k) ≠ a + b + c - 1 := by
  by_cases hkb : k < b <;>
    simp [clipAPoint, rankLevel, hkb] <;> omega

private theorem clipAPoint_second_ne_zero
    (a b k : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b)
    (hk : k < a + b - 1) :
    (clipAPoint a b k).second ≠ 0 := by
  by_cases hkb : k < b <;>
    simp [clipAPoint, hkb] <;> omega

private theorem clipForwardAPoint_first_ne_zero (a b k : ℕ) :
    (clipForwardAPoint a b k).first ≠ 0 := by
  by_cases hkb : k < b <;>
    simp [clipForwardAPoint, hkb]

/-- Every explicitly listed lost dart was an internal patch contact before clipping. -/
theorem clipLostDarts_subset_patchContactDarts
    (a b c k : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a ≤ b) (hk : k < a + b - 1) :
    clipLostDarts a b k ⊆ patchContactDarts a b c := by
  intro pd hpd
  simp only [clipLostDarts, Finset.mem_insert, Finset.mem_singleton] at hpd
  rcases hpd with rfl | rfl | rfl
  · have hp := clipAPoint_mem_aRankPatch a b c k ha hb hc hab hk
    have htop := clipAPoint_rankLevel_ne_top a b c k ha hc hk
    simp [patchContactDarts, sameContactPoints, hp, htop]
  · have hp := clipAPoint_mem_aRankPatch a b c k ha hb hc hab hk
    have hsecond := clipAPoint_second_ne_zero a b k ha hb hab hk
    simp [patchContactDarts, diagonalContactPoints, hp, hsecond]
  · have hp := clipForwardAPoint_mem_aRankPatch a b c k ha hb hc hab hk
    have hfirst := clipForwardAPoint_first_ne_zero a b k
    simp [patchContactDarts, horizontalContactPoints, hp, hfirst]

/-- Every lost dart from a valid clipping budget is a contact of the original patch. -/
theorem clippedLostDarts_subset_patchContactDarts
    (a b c d : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a ≤ b) (hd : d ≤ a + b - 1) :
    clippedLostDarts a b d ⊆ patchContactDarts a b c := by
  intro pd hpd
  rcases Finset.mem_biUnion.mp hpd with ⟨k, hk, hpdk⟩
  exact clipLostDarts_subset_patchContactDarts a b c k ha hb hc hab
    (lt_of_lt_of_le (Finset.mem_range.mp hk) hd) hpdk

private theorem clipA_horizontal_eq_forward_pred
    (a b k : ℕ) (hk : 0 < k) (htrans : k ≠ b) :
    clipAPoint a b k = clipForwardAPoint a b (k - 1) := by
  by_cases hkb : k < b
  · have hpred : k - 1 < b := by omega
    apply RankPoint.ext <;>
      simp [clipAPoint, clipForwardAPoint, hkb, hpred] <;> omega
  · have hpred : ¬ k - 1 < b := by omega
    apply RankPoint.ext <;>
      simp [clipAPoint, clipForwardAPoint, hkb, hpred] <;> omega

private theorem same_base_of_clipB
    {a b k : ℕ} {p : RankPoint}
    (h : rankDartNeighbor (p, .same) = clipBPoint a b k) :
    p.first = (clipBPoint a b k).first ∧
      p.second = (clipBPoint a b k).second := by
  simpa [rankDartNeighbor, sameRankNeighbor] using congrArg
    (fun q : RankPoint => (q.first, q.second)) h

private theorem horizontal_base_of_clipB
    {a b k : ℕ} {p : RankPoint} (hpSide : p.side = false) (hp : p.first ≠ 0)
    (h : rankDartNeighbor (p, .horizontal) = clipBPoint a b k) :
    p = clipForwardAPoint a b k := by
  by_cases hkb : k < b
  · apply RankPoint.ext
    · have hf := congrArg RankPoint.first h
      simp [rankDartNeighbor, horizontalRankNeighbor, clipBPoint,
        clipForwardAPoint, hkb] at hf ⊢
      omega
    · have hs := congrArg RankPoint.second h
      simpa [rankDartNeighbor, horizontalRankNeighbor, clipBPoint,
        clipForwardAPoint, hkb] using hs
    · exact hpSide.trans (clipForwardAPoint_side a b k).symm
  · apply RankPoint.ext
    · have hf := congrArg RankPoint.first h
      simp [rankDartNeighbor, horizontalRankNeighbor, clipBPoint,
        clipForwardAPoint, hkb] at hf ⊢
      omega
    · have hs := congrArg RankPoint.second h
      simpa [rankDartNeighbor, horizontalRankNeighbor, clipBPoint,
        clipForwardAPoint, hkb] using hs
    · exact hpSide.trans (clipForwardAPoint_side a b k).symm

private theorem diagonal_base_of_clipB
    {a b k : ℕ} {p : RankPoint} (hpSide : p.side = false) (hp : p.second ≠ 0)
    (h : rankDartNeighbor (p, .diagonal) = clipBPoint a b k) :
    p = clipAPoint a b k := by
  by_cases hkb : k < b
  · apply RankPoint.ext
    · have hf := congrArg RankPoint.first h
      simpa [rankDartNeighbor, diagonalRankNeighbor, clipBPoint,
        clipAPoint, hkb] using hf
    · have hs := congrArg RankPoint.second h
      simp [rankDartNeighbor, diagonalRankNeighbor, clipBPoint,
        clipAPoint, hkb] at hs ⊢
      omega
    · exact hpSide.trans (clipAPoint_side a b k).symm
  · apply RankPoint.ext
    · have hf := congrArg RankPoint.first h
      simpa [rankDartNeighbor, diagonalRankNeighbor, clipBPoint,
        clipAPoint, hkb] using hf
    · have hs := congrArg RankPoint.second h
      simp [rankDartNeighbor, diagonalRankNeighbor, clipBPoint,
        clipAPoint, hkb] at hs ⊢
      omega
    · exact hpSide.trans (clipAPoint_side a b k).symm

private theorem patchContactDart_base_side
    {a b c : ℕ} {pd : RankPoint × Direction}
    (hpd : pd ∈ patchContactDarts a b c) : pd.1.side = false := by
  rcases pd with ⟨p, direction⟩
  cases direction
  · have hp : p ∈ sameContactPoints a b c := by
      simpa [patchContactDarts] using hpd
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
  · have hp : p ∈ horizontalContactPoints a b c := by
      simpa [patchContactDarts] using hpd
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
  · have hp : p ∈ diagonalContactPoints a b c := by
      simpa [patchContactDarts] using hpd
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2

/-- A patch contact is destroyed by clipping exactly when one of its endpoints is clipped. -/
theorem mem_clippedLostDarts_iff
    (a b c d : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a ≤ b) (hd : d ≤ a + b - 1)
    {pd : RankPoint × Direction} (hpd : pd ∈ patchContactDarts a b c) :
    pd ∈ clippedLostDarts a b d ↔
      pd.1 ∈ clippedRankPoints a b d ∨
        rankDartNeighbor pd ∈ clippedRankPoints a b d := by
  constructor
  · intro hlost
    rcases Finset.mem_biUnion.mp hlost with ⟨k, hk, hpdk⟩
    have hk' : k < d := Finset.mem_range.mp hk
    simp only [clipLostDarts, Finset.mem_insert, Finset.mem_singleton] at hpdk
    rcases hpdk with rfl | rfl | rfl
    · left
      exact mem_clippedRankPoints_iff.mpr ⟨k, hk', Or.inr rfl⟩
    · left
      exact mem_clippedRankPoints_iff.mpr ⟨k, hk', Or.inr rfl⟩
    · right
      rw [rankDartNeighbor_clipForward_horizontal]
      exact mem_clippedRankPoints_iff.mpr ⟨k, hk', Or.inl rfl⟩
  · rintro (hbase | hneighbor)
    · have hbaseSide := patchContactDart_base_side hpd
      rcases mem_clippedRankPoints_iff.mp hbase with ⟨k, hk, hpk | hpk⟩
      · have hs := congrArg RankPoint.side hpk
        rw [hbaseSide] at hs
        simp at hs
      · rcases pd with ⟨p, direction⟩
        subst p
        apply Finset.mem_biUnion.mpr
        cases direction
        · exact ⟨k, Finset.mem_range.mpr hk, by simp [clipLostDarts]⟩
        · have hpHorizontal : clipAPoint a b k ∈ horizontalContactPoints a b c := by
            simpa [patchContactDarts] using hpd
          have hfirst : (clipAPoint a b k).first ≠ 0 :=
            (Finset.mem_filter.mp hpHorizontal).2
          have hkpos : 0 < k := by
            by_cases hkb : k < b <;> simp [clipAPoint, hkb] at hfirst <;> omega
          have htrans : k ≠ b := by
            intro hkb
            subst k
            simp [clipAPoint] at hfirst
          have hpred : k - 1 < d := by omega
          refine ⟨k - 1, Finset.mem_range.mpr hpred, ?_⟩
          have heq := clipA_horizontal_eq_forward_pred a b k hkpos htrans
          simp [clipLostDarts, heq]
        · exact ⟨k, Finset.mem_range.mpr hk, by simp [clipLostDarts]⟩
    · rcases mem_clippedRankPoints_iff.mp hneighbor with ⟨k, hk, hpk | hpk⟩
      · rcases pd with ⟨p, direction⟩
        cases direction
        · have hpSame : p ∈ sameContactPoints a b c := by
            simpa [patchContactDarts] using hpd
          have hpA := (Finset.mem_filter.mp hpSame).1
          have hpSide := (Finset.mem_filter.mp hpA).2
          have hcoords := same_base_of_clipB hpk
          by_cases hkb : k < b
          · have hpPatch := (Finset.mem_filter.mp hpA).1
            rw [mem_rankPatch] at hpPatch
            have hfirst := hcoords.1
            have hsecond := hcoords.2
            simp [clipBPoint, hkb] at hfirst hsecond
            rcases p with ⟨i, j, side⟩
            simp [rankLevel] at hpSide hpPatch
            omega
          · let h := k - b
            have hkmax : k < a + b - 1 := lt_of_lt_of_le hk hd
            have hh : h < b := by
              dsimp [h]
              omega
            have hpEq : p = clipAPoint a b h := by
              apply RankPoint.ext
              · simpa [clipAPoint, hh, clipBPoint, hkb, h] using hcoords.1
              · simpa [clipAPoint, hh, clipBPoint, hkb, h] using hcoords.2
              · exact hpSide.trans (clipAPoint_side a b h).symm
            have hhd : h < d := by dsimp [h]; omega
            subst p
            exact Finset.mem_biUnion.mpr
              ⟨h, Finset.mem_range.mpr hhd, by simp [clipLostDarts]⟩
        · have hpHorizontal : p ∈ horizontalContactPoints a b c := by
            simpa [patchContactDarts] using hpd
          have hpA := (Finset.mem_filter.mp hpHorizontal).1
          have hpSide := (Finset.mem_filter.mp hpA).2
          have hfirst := (Finset.mem_filter.mp hpHorizontal).2
          have hpEq := horizontal_base_of_clipB hpSide hfirst hpk
          subst p
          exact Finset.mem_biUnion.mpr
            ⟨k, Finset.mem_range.mpr hk, by simp [clipLostDarts]⟩
        · have hpDiagonal : p ∈ diagonalContactPoints a b c := by
            simpa [patchContactDarts] using hpd
          have hpA := (Finset.mem_filter.mp hpDiagonal).1
          have hpSide := (Finset.mem_filter.mp hpA).2
          have hsecond := (Finset.mem_filter.mp hpDiagonal).2
          have hpEq := diagonal_base_of_clipB hpSide hsecond hpk
          subst p
          exact Finset.mem_biUnion.mpr
            ⟨k, Finset.mem_range.mpr hk, by simp [clipLostDarts]⟩
      · have hs := congrArg RankPoint.side hpk
        simp [rankDartNeighbor_side] at hs

end OeisA263135
