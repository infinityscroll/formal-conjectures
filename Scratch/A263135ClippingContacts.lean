import Scratch.A263135RankDarts

namespace OeisA263135

@[simp]
theorem rankPointVertex_mem_clippedPatch_iff
    {a b c d : ℕ} {p : RankPoint} :
    rankPointVertex p ∈ clippedPatch a b c d ↔
      p ∈ rankPatch a b c ∧ p ∉ clippedRankPoints a b d := by
  constructor
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨q, hq, heq⟩
    have hqp : q = p := rankPointVertex_injective heq
    subst q
    exact Finset.mem_sdiff.mp hq
  · intro hp
    exact Finset.mem_image.mpr ⟨p, Finset.mem_sdiff.mpr hp, rfl⟩

/-- The clipped patch is a subset of the original convex patch. -/
theorem clippedPatch_subset_patch (a b c d : ℕ) :
    clippedPatch a b c d ⊆ patch a b c := by
  intro v hv
  rcases Finset.mem_image.mp hv with ⟨p, hp, rfl⟩
  exact Finset.mem_image.mpr ⟨p, Finset.sdiff_subset hp, rfl⟩

private theorem aInternalDarts_mono
    {S T : Finset Vertex} (hST : S ⊆ T) :
    aInternalDarts S ⊆ aInternalDarts T := by
  intro vd hvd
  rcases Finset.mem_filter.mp hvd with ⟨hint, hside⟩
  rcases Finset.mem_filter.mp hint with ⟨hprod, hn⟩
  rcases Finset.mem_product.mp hprod with ⟨hv, hd⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
    ⟨hST hv, hd⟩, hST hn⟩, hside⟩

/-- Ranked contacts which survive all `d` clipping steps. -/
def survivingPatchContactDarts (a b c d : ℕ) : Finset (RankPoint × Direction) :=
  patchContactDarts a b c \ clippedLostDarts a b d

private theorem rankDartNeighbor_mem_rankPatch
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    {pd : RankPoint × Direction} (hpd : pd ∈ patchContactDarts a b c) :
    rankDartNeighbor pd ∈ rankPatch a b c := by
  have hint := (clippingRankDart_mem_aInternal_iff ha hb hc).mp hpd
  rcases Finset.mem_filter.mp hint with ⟨hint, hside⟩
  rcases Finset.mem_filter.mp hint with ⟨hprod, hn⟩
  rw [neighbor_clippingRankDart_eq hpd] at hn
  exact rankPointVertex_mem_patch_iff.mp hn

/-- For a contact of the original patch, survival is equivalent to both endpoints
remaining after clipping. -/
theorem clippingRankDart_mem_clipped_iff
    (a b c d : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    {pd : RankPoint × Direction} (hpd : pd ∈ patchContactDarts a b c) :
    clippingRankDartVertex pd ∈ aInternalDarts (clippedPatch a b c d) ↔
      pd.1 ∉ clippedRankPoints a b d ∧
        rankDartNeighbor pd ∉ clippedRankPoints a b d := by
  have hpPatch : pd.1 ∈ rankPatch a b c := by
    have hint := (clippingRankDart_mem_aInternal_iff ha hb hc).mp hpd
    rcases Finset.mem_filter.mp hint with ⟨hint, hside⟩
    rcases Finset.mem_filter.mp hint with ⟨hprod, hn⟩
    exact rankPointVertex_mem_patch_iff.mp (Finset.mem_product.mp hprod).1
  have hnPatch := rankDartNeighbor_mem_rankPatch ha hb hc hpd
  constructor
  · intro hint
    rcases Finset.mem_filter.mp hint with ⟨hint, hside⟩
    rcases Finset.mem_filter.mp hint with ⟨hprod, hn⟩
    have hpClip := (rankPointVertex_mem_clippedPatch_iff.mp
      (Finset.mem_product.mp hprod).1).2
    rw [neighbor_clippingRankDart_eq hpd] at hn
    have hnClip := (rankPointVertex_mem_clippedPatch_iff.mp hn).2
    exact ⟨hpClip, hnClip⟩
  · rintro ⟨hpClip, hnClip⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨rankPointVertex_mem_clippedPatch_iff.mpr ⟨hpPatch, hpClip⟩,
        Finset.mem_univ _⟩, ?_⟩, ?_⟩
    · rw [neighbor_clippingRankDart_eq hpd]
      exact rankPointVertex_mem_clippedPatch_iff.mpr ⟨hnPatch, hnClip⟩
    · have hfull := (clippingRankDart_mem_aInternal_iff ha hb hc).mp hpd
      exact (Finset.mem_filter.mp hfull).2

/-- The surviving ranked contacts are exactly the A-based internal darts of the
clipped concrete patch. -/
theorem surviving_mem_aInternal_iff
    (a b c d : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a ≤ b) (hd : d ≤ a + b - 1)
    {pd : RankPoint × Direction} :
    pd ∈ survivingPatchContactDarts a b c d ↔
      clippingRankDartVertex pd ∈ aInternalDarts (clippedPatch a b c d) := by
  constructor
  · intro hsurvive
    rcases Finset.mem_sdiff.mp hsurvive with ⟨hpd, hnotLost⟩
    apply (clippingRankDart_mem_clipped_iff a b c d ha hb hc hpd).mpr
    have hnotEndpoints :
        ¬(pd.1 ∈ clippedRankPoints a b d ∨
          rankDartNeighbor pd ∈ clippedRankPoints a b d) := by
      intro h
      exact hnotLost ((mem_clippedLostDarts_iff a b c d ha hb hc hab hd hpd).mpr h)
    exact not_or.mp hnotEndpoints
  · intro hint
    have hfull := aInternalDarts_mono (clippedPatch_subset_patch a b c d) hint
    have hpd : pd ∈ patchContactDarts a b c :=
      (clippingRankDart_mem_aInternal_iff ha hb hc).mpr hfull
    apply Finset.mem_sdiff.mpr
    refine ⟨hpd, ?_⟩
    have hendpoints :=
      (clippingRankDart_mem_clipped_iff a b c d ha hb hc hpd).mp hint
    intro hlost
    have h := (mem_clippedLostDarts_iff a b c d ha hb hc hab hd hpd).mp hlost
    exact (not_or.mpr hendpoints) h

/-- The ranked patch-contact list has cardinality equal to the original contact count. -/
theorem card_patchContactDarts_eq_contacts
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (patchContactDarts a b c).card = contacts (patch a b c) := by
  rw [contacts_eq_card_aInternalDarts]
  apply Finset.card_bij (fun pd hpd => clippingRankDartVertex pd)
  · exact fun pd hpd => (clippingRankDart_mem_aInternal_iff ha hb hc).mp hpd
  · intro p hp q hq h
    exact clippingRankDartVertex_injective h
  · intro vd hvd
    rcases vd with ⟨v, direction⟩
    rcases Finset.mem_filter.mp hvd with ⟨hint, hside⟩
    rcases Finset.mem_filter.mp hint with ⟨hprod, hn⟩
    rcases Finset.mem_image.mp (Finset.mem_product.mp hprod).1 with ⟨p, hp, rfl⟩
    refine ⟨(p, direction), (clippingRankDart_mem_aInternal_iff ha hb hc).mpr ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨hint, hside⟩

/-- Contact count of a clipped patch is the number of surviving ranked darts. -/
theorem contacts_clippedPatch_eq_card_surviving
    (a b c d : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a ≤ b) (hd : d ≤ a + b - 1) :
    contacts (clippedPatch a b c d) =
      (survivingPatchContactDarts a b c d).card := by
  rw [contacts_eq_card_aInternalDarts]
  symm
  apply Finset.card_bij (fun pd hpd => clippingRankDartVertex pd)
  · exact fun pd hpd =>
      (surviving_mem_aInternal_iff a b c d ha hb hc hab hd).mp hpd
  · intro p hp q hq h
    exact clippingRankDartVertex_injective h
  · intro vd hvd
    rcases vd with ⟨v, direction⟩
    rcases Finset.mem_filter.mp hvd with ⟨hint, hside⟩
    rcases Finset.mem_filter.mp hint with ⟨hprod, hn⟩
    rcases Finset.mem_image.mp (Finset.mem_product.mp hprod).1 with ⟨p, hp, rfl⟩
    refine ⟨(p, direction), ?_, rfl⟩
    exact (surviving_mem_aInternal_iff a b c d ha hb hc hab hd).mpr
      (Finset.mem_filter.mpr ⟨hint, hside⟩)

/-- Exact contact count after `d` valid clipping steps. -/
theorem contacts_clippedPatch_formula
    (a b c d : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a ≤ b) (hd : d ≤ a + b - 1) :
    contacts (clippedPatch a b c d) =
      3 * (a * b + b * c + c * a - d) - (a + b + c) := by
  have hlost_le := Finset.card_le_card
    (clippedLostDarts_subset_patchContactDarts a b c d ha hb hc hab hd)
  rw [card_clippedLostDarts a b d hd,
    card_patchContactDarts_eq_contacts a b c ha hb hc,
    contacts_patch_formula a b c ha hb hc] at hlost_le
  rw [contacts_clippedPatch_eq_card_surviving a b c d ha hb hc hab hd]
  unfold survivingPatchContactDarts
  rw [Finset.card_sdiff_of_subset
    (clippedLostDarts_subset_patchContactDarts a b c d ha hb hc hab hd),
    card_clippedLostDarts a b d hd,
    card_patchContactDarts_eq_contacts a b c ha hb hc,
    contacts_patch_formula a b c ha hb hc]
  omega

end OeisA263135
