import Scratch.A263135Parameters

namespace OeisA263135

/-- Finite coordinate box used for the convex honeycomb patch. -/
def rankBox (A B : ℕ) : Finset ((ℕ × ℕ) × Bool) :=
  (Finset.range A ×ˢ Finset.range B) ×ˢ Finset.univ

/-- Convert a boxed coordinate triple into a ranked honeycomb point. -/
def tripleRankPoint (x : (ℕ × ℕ) × Bool) : RankPoint :=
  ⟨x.1.1, x.1.2, x.2⟩

theorem tripleRankPoint_injective : Function.Injective tripleRankPoint := by
  rintro ⟨⟨i, j⟩, s⟩ ⟨⟨k, l⟩, t⟩ h
  simp [tripleRankPoint] at h ⊢
  exact h

/-- Integer level of a ranked honeycomb point in the diagonal row direction. -/
def rankLevel (p : RankPoint) : ℕ := p.first + p.second + if p.side then 1 else 0

/-- Convex patch with alternating side parameters `a,b,c,a,b,c`, in ranked coordinates. -/
def rankPatch (a b c : ℕ) : Finset RankPoint :=
  ((rankBox (a + b) (b + c)).filter fun x =>
      b ≤ rankLevel (tripleRankPoint x) ∧
        rankLevel (tripleRankPoint x) < b + (a + c)).image tripleRankPoint

/-- Convert ranked coordinates to the honeycomb coordinates used by `Vertex`. -/
def rankPointVertex (p : RankPoint) : Vertex :=
  ⟨p.first, (p.second : ℤ) - 1, p.side⟩

theorem rankPointVertex_injective : Function.Injective rankPointVertex := by
  intro p q h
  apply RankPoint.ext
  · have hi := congrArg Vertex.i h
    exact_mod_cast hi
  · have hj := congrArg Vertex.j h
    omega
  · exact congrArg Vertex.side h

/-- The concrete finite honeycomb patch. -/
def patch (a b c : ℕ) : Finset Vertex :=
  (rankPatch a b c).image rankPointVertex

@[simp]
theorem card_patch (a b c : ℕ) :
    (patch a b c).card = (rankPatch a b c).card := by
  exact Finset.card_image_of_injective _ rankPointVertex_injective

@[simp]
theorem rowCoord_rankPointVertex_first (p : RankPoint) :
    rowCoord .first (rankPointVertex p) = p.first := by
  simp [rankPointVertex, rowCoord]

@[simp]
theorem rowCoord_rankPointVertex_second (p : RankPoint) :
    rowCoord .second (rankPointVertex p) = (p.second : ℤ) - 1 := by
  simp [rankPointVertex, rowCoord]

@[simp]
theorem rowCoord_rankPointVertex_diagonal (p : RankPoint) :
    rowCoord .diagonal (rankPointVertex p) = (rankLevel p : ℤ) - 1 := by
  rcases p with ⟨i, j, side⟩
  cases side <;> simp [rankPointVertex, rowCoord, rankLevel] <;> omega

/-- Lower clipped corner pair, in ranked coordinates. -/
def clipPair (a b : ℕ) (k : ℕ) : Finset RankPoint :=
  if k < b then
    {⟨k, b - 1 - k, true⟩, ⟨k, b - k, false⟩}
  else
    let h := k - b
    {⟨h, b - h, true⟩, ⟨h, b + 1 - h, false⟩}

/-- All pairs removed in the first `d` corner-clipping steps. -/
def clippedRankPoints (a b d : ℕ) : Finset RankPoint :=
  (Finset.range d).biUnion fun k => clipPair a b k

/-- Patch after `d` successive corner-pair removals. -/
def clippedPatch (a b c d : ℕ) : Finset Vertex :=
  ((rankPatch a b c) \ clippedRankPoints a b d).image rankPointVertex

end OeisA263135
