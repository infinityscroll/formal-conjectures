import Scratch.A263135ClippingCard

namespace OeisA263135

/-- B-side point removed at clipping step `k`. -/
def clipBPoint (a b k : ℕ) : RankPoint :=
  if k < b then
    ⟨k, b - 1 - k, true⟩
  else
    let h := k - b
    ⟨h, b - h, true⟩

/-- A-side point removed at clipping step `k`. -/
def clipAPoint (a b k : ℕ) : RankPoint :=
  if k < b then
    ⟨k, b - k, false⟩
  else
    let h := k - b
    ⟨h, b + 1 - h, false⟩

/-- The A-side point immediately forward of the removed B point. -/
def clipForwardAPoint (a b k : ℕ) : RankPoint :=
  if k < b then
    ⟨k + 1, b - 1 - k, false⟩
  else
    let h := k - b
    ⟨h + 1, b - h, false⟩

@[simp]
theorem clipPair_eq (a b k : ℕ) :
    clipPair a b k = {clipBPoint a b k, clipAPoint a b k} := by
  unfold clipPair clipBPoint clipAPoint
  split_ifs <;> rfl

/-- The three A-based internal darts destroyed by clipping pair `k`.

They are the same and diagonal darts based at the removed A point, together
with the horizontal dart entering the removed B point from the forward A point.
-/
def clipLostDarts (a b k : ℕ) : Finset (RankPoint × Direction) :=
  {(clipAPoint a b k, .same),
    (clipAPoint a b k, .diagonal),
    (clipForwardAPoint a b k, .horizontal)}

@[simp]
theorem card_clipLostDarts (a b k : ℕ) :
    (clipLostDarts a b k).card = 3 := by
  simp [clipLostDarts]

private theorem clipAPoint_injective_on
    {a b k l : ℕ} (hk : k < a + b - 1) (hl : l < a + b - 1)
    (h : clipAPoint a b k = clipAPoint a b l) : k = l := by
  by_cases hkb : k < b <;> by_cases hlb : l < b <;>
    simp [clipAPoint, hkb, hlb] at h <;> omega

private theorem clipForwardAPoint_injective_on
    {a b k l : ℕ} (hk : k < a + b - 1) (hl : l < a + b - 1)
    (h : clipForwardAPoint a b k = clipForwardAPoint a b l) : k = l := by
  by_cases hkb : k < b <;> by_cases hlb : l < b <;>
    simp [clipForwardAPoint, hkb, hlb] at h <;> omega

private theorem clipLostDarts_pairwise_disjoint
    (a b d : ℕ) (hd : d ≤ a + b - 1) :
    (Finset.range d).toSet.PairwiseDisjoint (clipLostDarts a b) := by
  intro k hk l hl hkl
  have hkd : k < a + b - 1 := lt_of_lt_of_le (Finset.mem_range.mp hk) hd
  have hld : l < a + b - 1 := lt_of_lt_of_le (Finset.mem_range.mp hl) hd
  rw [Finset.disjoint_left]
  intro pd hpk hpl
  simp only [clipLostDarts, Finset.mem_insert, Finset.mem_singleton] at hpk hpl
  rcases hpk with hpk | hpk | hpk <;>
    rcases hpl with hpl | hpl | hpl
  · exact hkl (clipAPoint_injective_on hkd hld
      (congrArg Prod.fst (hpk.symm.trans hpl)))
  · have := congrArg Prod.snd (hpk.symm.trans hpl)
    simp at this
  · have := congrArg Prod.snd (hpk.symm.trans hpl)
    simp at this
  · have := congrArg Prod.snd (hpk.symm.trans hpl)
    simp at this
  · exact hkl (clipAPoint_injective_on hkd hld
      (congrArg Prod.fst (hpk.symm.trans hpl)))
  · have := congrArg Prod.snd (hpk.symm.trans hpl)
    simp at this
  · have := congrArg Prod.snd (hpk.symm.trans hpl)
    simp at this
  · have := congrArg Prod.snd (hpk.symm.trans hpl)
    simp at this
  · exact hkl (clipForwardAPoint_injective_on hkd hld
      (congrArg Prod.fst (hpk.symm.trans hpl)))

/-- All A-based contact darts destroyed by the first `d` clipping steps. -/
def clippedLostDarts (a b d : ℕ) : Finset (RankPoint × Direction) :=
  (Finset.range d).biUnion fun k => clipLostDarts a b k

/-- Exactly three distinct contact darts are destroyed per clipping pair. -/
theorem card_clippedLostDarts
    (a b d : ℕ) (hd : d ≤ a + b - 1) :
    (clippedLostDarts a b d).card = 3 * d := by
  rw [clippedLostDarts, Finset.card_biUnion]
  · simp [card_clipLostDarts, mul_comm]
  · exact clipLostDarts_pairwise_disjoint a b d hd

end OeisA263135
