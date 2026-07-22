import Scratch.A263135Boundary

namespace OeisA263135

/-- Vertices of `S` lying on the row `x` of kind `r`. -/
def rowSlice (r : RowKind) (S : Finset Vertex) (x : ℤ) : Finset Vertex :=
  S.filter fun v => rowCoord r v = x

private theorem rowSlice_nonempty (r : RowKind) (S : Finset Vertex)
    (x : ↥(occupiedRows r S)) : (rowSlice r S x).Nonempty := by
  rcases Finset.mem_image.mp x.property with ⟨v, hvS, hvx⟩
  exact ⟨v, Finset.mem_filter.mpr ⟨hvS, hvx⟩⟩

private theorem exists_min_vertex (r : RowKind) (S : Finset Vertex)
    (x : ↥(occupiedRows r S)) :
    ∃ v : Vertex,
      v ∈ S ∧ rowCoord r v = x ∧
        ∀ w ∈ S, rowCoord r w = x → alongCoord r v ≤ alongCoord r w := by
  let T := rowSlice r S x
  have hT : T.Nonempty := rowSlice_nonempty r S x
  let A := T.image (alongCoord r)
  have hA : A.Nonempty := hT.image _
  have hm : A.min' hA ∈ A := A.min'_mem hA
  rcases Finset.mem_image.mp hm with ⟨v, hvT, hv⟩
  refine ⟨v, (Finset.mem_filter.mp hvT).1, (Finset.mem_filter.mp hvT).2, ?_⟩
  intro w hwS hwx
  have hwT : w ∈ T := Finset.mem_filter.mpr ⟨hwS, hwx⟩
  have hwA : alongCoord r w ∈ A := Finset.mem_image.mpr ⟨w, hwT, rfl⟩
  have hle := A.min'_le (alongCoord r w) hwA
  simpa [hv] using hle

private theorem exists_max_vertex (r : RowKind) (S : Finset Vertex)
    (x : ↥(occupiedRows r S)) :
    ∃ v : Vertex,
      v ∈ S ∧ rowCoord r v = x ∧
        ∀ w ∈ S, rowCoord r w = x → alongCoord r w ≤ alongCoord r v := by
  let T := rowSlice r S x
  have hT : T.Nonempty := rowSlice_nonempty r S x
  let A := T.image (alongCoord r)
  have hA : A.Nonempty := hT.image _
  have hm : A.max' hA ∈ A := A.max'_mem hA
  rcases Finset.mem_image.mp hm with ⟨v, hvT, hv⟩
  refine ⟨v, (Finset.mem_filter.mp hvT).1, (Finset.mem_filter.mp hvT).2, ?_⟩
  intro w hwS hwx
  have hwT : w ∈ T := Finset.mem_filter.mpr ⟨hwS, hwx⟩
  have hwA : alongCoord r w ∈ A := Finset.mem_image.mpr ⟨w, hwT, rfl⟩
  have hle := A.le_max' (alongCoord r w) hwA
  simpa [hv] using hle

noncomputable def minRowVertex (r : RowKind) (S : Finset Vertex)
    (x : ↥(occupiedRows r S)) : Vertex :=
  Classical.choose (exists_min_vertex r S x)

noncomputable def maxRowVertex (r : RowKind) (S : Finset Vertex)
    (x : ↥(occupiedRows r S)) : Vertex :=
  Classical.choose (exists_max_vertex r S x)

private theorem minRowVertex_spec (r : RowKind) (S : Finset Vertex)
    (x : ↥(occupiedRows r S)) :
    minRowVertex r S x ∈ S ∧ rowCoord r (minRowVertex r S x) = x ∧
      ∀ w ∈ S, rowCoord r w = x →
        alongCoord r (minRowVertex r S x) ≤ alongCoord r w :=
  Classical.choose_spec (exists_min_vertex r S x)

private theorem maxRowVertex_spec (r : RowKind) (S : Finset Vertex)
    (x : ↥(occupiedRows r S)) :
    maxRowVertex r S x ∈ S ∧ rowCoord r (maxRowVertex r S x) = x ∧
      ∀ w ∈ S, rowCoord r w = x →
        alongCoord r w ≤ alongCoord r (maxRowVertex r S x) :=
  Classical.choose_spec (exists_max_vertex r S x)

private theorem prev_minRowVertex_not_mem (r : RowKind) (S : Finset Vertex)
    (x : ↥(occupiedRows r S)) :
    neighbor (minRowVertex r S x) (prevDirection r (minRowVertex r S x)) ∉ S := by
  intro hmem
  have hmin := (minRowVertex_spec r S x).2.2 _ hmem (by simp)
  rw [alongCoord_neighbor_prev] at hmin
  omega

private theorem next_maxRowVertex_not_mem (r : RowKind) (S : Finset Vertex)
    (x : ↥(occupiedRows r S)) :
    neighbor (maxRowVertex r S x) (nextDirection r (maxRowVertex r S x)) ∉ S := by
  intro hmem
  have hmax := (maxRowVertex_spec r S x).2.2 _ hmem (by simp)
  rw [alongCoord_neighbor_next] at hmax
  omega

/-- The lower or upper outgoing dart associated to an occupied row. -/
noncomputable def endpointDart (r : RowKind) (S : Finset Vertex)
    (xb : ↥(occupiedRows r S) × Bool) : Vertex × Direction :=
  if xb.2 then
    let v := maxRowVertex r S xb.1
    (v, nextDirection r v)
  else
    let v := minRowVertex r S xb.1
    (v, prevDirection r v)

private theorem endpointDart_mem (r : RowKind) (S : Finset Vertex)
    (xb : ↥(occupiedRows r S) × Bool) : endpointDart r S xb ∈ rowBoundaryDarts r S := by
  classical
  rcases xb with ⟨x, side⟩
  cases side
  · simp only [endpointDart, Bool.false_eq_true, ↓reduceIte]
    let v := minRowVertex r S x
    have hvS : v ∈ S := (minRowVertex_spec r S x).1
    have hout : neighbor v (prevDirection r v) ∉ S := prev_minRowVertex_not_mem r S x
    have hrow : r ∈ preservedRows (v, prevDirection r v) := by
      simp [preservedRows]
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hvS, Finset.mem_univ _⟩, hout⟩, hrow⟩
  · simp only [endpointDart, ↓reduceIte]
    let v := maxRowVertex r S x
    have hvS : v ∈ S := (maxRowVertex_spec r S x).1
    have hout : neighbor v (nextDirection r v) ∉ S := next_maxRowVertex_not_mem r S x
    have hrow : r ∈ preservedRows (v, nextDirection r v) := by
      simp [preservedRows]
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hvS, Finset.mem_univ _⟩, hout⟩, hrow⟩

private theorem endpointDart_injective (r : RowKind) (S : Finset Vertex) :
    Function.Injective (endpointDart r S) := by
  intro a b hab
  rcases a with ⟨x, sx⟩
  rcases b with ⟨y, sy⟩
  cases sx <;> cases sy
  · apply Prod.ext
    · apply Subtype.ext
      have hv := congrArg (fun vd => rowCoord r vd.1) hab
      simpa [endpointDart, (minRowVertex_spec r S x).2.1,
        (minRowVertex_spec r S y).2.1] using hv
    · rfl
  · exfalso
    have hv := congrArg Prod.fst hab
    have hd := congrArg Prod.snd hab
    simp only [endpointDart, Bool.false_eq_true, ↓reduceIte] at hv hd
    rw [hv] at hd
    exact prevDirection_ne_nextDirection r _ hd
  · exfalso
    have hv := congrArg Prod.fst hab
    have hd := congrArg Prod.snd hab
    simp only [endpointDart, Bool.false_eq_true, ↓reduceIte] at hv hd
    rw [hv] at hd
    exact prevDirection_ne_nextDirection r _ hd.symm
  · apply Prod.ext
    · apply Subtype.ext
      have hv := congrArg (fun vd => rowCoord r vd.1) hab
      simpa [endpointDart, (maxRowVertex_spec r S x).2.1,
        (maxRowVertex_spec r S y).2.1] using hv
    · rfl

/-- Every occupied row contributes two distinct boundary darts. -/
theorem two_mul_occupiedRows_card_le_rowBoundaryDarts_card
    (r : RowKind) (S : Finset Vertex) :
    2 * (occupiedRows r S).card ≤ (rowBoundaryDarts r S).card := by
  classical
  let f : (↥(occupiedRows r S) × Bool) → ↥(rowBoundaryDarts r S) :=
    fun xb => ⟨endpointDart r S xb, endpointDart_mem r S xb⟩
  have hf : Function.Injective f := by
    intro a b h
    exact endpointDart_injective r S (Subtype.ext_iff.mp h)
  have hcard := Fintype.card_le_of_injective f hf
  simpa [f, mul_comm] using hcard

end OeisA263135
