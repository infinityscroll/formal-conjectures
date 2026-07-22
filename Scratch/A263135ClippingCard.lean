import Scratch.A263135PatchContacts

namespace OeisA263135

/-- The two vertices of a clipping pair are distinct. -/
theorem card_clipPair (a b k : ℕ) : (clipPair a b k).card = 2 := by
  unfold clipPair
  split_ifs <;> simp

private theorem clipPair_pairwise_disjoint
    (a b d : ℕ) (hd : d ≤ a + b - 1) :
    (Finset.range d).toSet.PairwiseDisjoint (clipPair a b) := by
  intro k hk l hl hkl
  have hkd : k < d := Finset.mem_range.mp hk
  have hld : l < d := Finset.mem_range.mp hl
  rw [Finset.disjoint_left]
  intro p hpk hpl
  by_cases hkb : k < b <;> by_cases hlb : l < b <;>
    simp [clipPair, hkb, hlb] at hpk hpl <;>
    rcases hpk with (rfl | rfl) <;> rcases hpl with h | h <;>
    simp at h <;> omega

/-- The first `d` clipping pairs contain exactly `2d` distinct ranked vertices. -/
theorem card_clippedRankPoints
    (a b d : ℕ) (hd : d ≤ a + b - 1) :
    (clippedRankPoints a b d).card = 2 * d := by
  rw [clippedRankPoints, Finset.card_biUnion]
  · simp [card_clipPair, mul_comm]
  · exact clipPair_pairwise_disjoint a b d hd

private theorem clipPair_subset_rankPatch
    (a b c k : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hk : k < a + b - 1) :
    clipPair a b k ⊆ rankPatch a b c := by
  intro p hp
  by_cases hkb : k < b
  · simp [clipPair, hkb] at hp
    rcases hp with rfl | rfl <;> rw [mem_rankPatch] <;>
      simp [rankLevel] <;> omega
  · have hbk : b ≤ k := Nat.le_of_not_gt hkb
    simp [clipPair, hkb] at hp
    rcases hp with rfl | rfl <;> rw [mem_rankPatch] <;>
      simp [rankLevel] <;> omega

/-- Every point removed by a valid clipping budget belongs to the original patch. -/
theorem clippedRankPoints_subset_rankPatch
    (a b c d : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : d ≤ a + b - 1) :
    clippedRankPoints a b d ⊆ rankPatch a b c := by
  intro p hp
  rcases Finset.mem_biUnion.mp hp with ⟨k, hk, hpk⟩
  exact clipPair_subset_rankPatch a b c k ha hb hc
    (lt_of_lt_of_le (Finset.mem_range.mp hk) hd) hpk

/-- Exact cardinality after `d` clipping steps. -/
theorem card_clippedPatch
    (a b c d : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : d ≤ a + b - 1) :
    (clippedPatch a b c d).card = 2 * (a * b + b * c + c * a - d) := by
  unfold clippedPatch
  rw [Finset.card_image_of_injective _ rankPointVertex_injective,
    Finset.card_sdiff_of_subset
      (clippedRankPoints_subset_rankPatch a b c d ha hb hc hd),
    card_rankPatch, card_clippedRankPoints a b d hd]
  omega

end OeisA263135
