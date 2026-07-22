import Scratch.A263135ChainOrder

namespace OeisA263135

/-- Finite key set indexing all long and short product chains. -/
def chainKeys (S : Finset Vertex) : Finset (ℕ × Bool) :=
  Finset.range (occupiedRows .first S).card ×ˢ Finset.univ

/-- Chain key of a selected honeycomb vertex. -/
noncomputable def vertexChainKey (S : Finset Vertex) (v : ↥S) : ℕ × Bool :=
  (vertexChainIndex S v, vertexSubchain S v)

/-- Vertices of `S` assigned to one product chain. -/
noncomputable def chainFiber (S : Finset Vertex) (k : ℕ × Bool) : Finset ↥S :=
  S.attach.filter fun v => vertexChainKey S v = k

/-- Sum of the long- and short-chain capacity bounds. -/
def chainCapSum (a b c : ℕ) : ℕ :=
  ∑ t ∈ Finset.range a,
    (min c (a + b - 2 * t) + min c (a + b - 2 - 2 * t))

private theorem vertexChainKey_mem (S : Finset Vertex) (v : ↥S) :
    vertexChainKey S v ∈ chainKeys S := by
  simp [vertexChainKey, chainKeys, vertexChainIndex_lt_firstRows]

/-- The selected vertices partition into product-chain fibers. -/
theorem card_eq_sum_chainFiber (S : Finset Vertex) :
    S.card = ∑ k ∈ chainKeys S, (chainFiber S k).card := by
  rw [← Finset.card_attach]
  exact Finset.card_eq_sum_card_fiberwise fun v _ => vertexChainKey_mem S v

private theorem chainFiber_key {S : Finset Vertex} {k : ℕ × Bool} {v : ↥S}
    (hv : v ∈ chainFiber S k) : vertexChainKey S v = k :=
  (Finset.mem_filter.mp hv).2

private theorem chainFiber_rankPoint_mem
    {S : Finset Vertex} {k : ℕ × Bool} {v : ↥S}
    (hab : (occupiedRows .first S).card ≤ (occupiedRows .second S).card)
    (hv : v ∈ chainFiber S k) :
    if k.2 then
      vertexRankPoint S v ∈
        shortBoxChain (occupiedRows .first S).card (occupiedRows .second S).card k.1
    else
      vertexRankPoint S v ∈
        longBoxChain (occupiedRows .first S).card (occupiedRows .second S).card k.1 := by
  have hchosen := vertexRankPoint_mem_chosenChain S v hab
  have hkey := chainFiber_key hv
  have ht := congrArg Prod.fst hkey
  have hs := congrArg Prod.snd hkey
  simpa [vertexChainKey, ht, hs] using hchosen

private theorem chainFiber_card_le_boxChain
    (S : Finset Vertex) (k : ℕ × Bool)
    (hab : (occupiedRows .first S).card ≤ (occupiedRows .second S).card) :
    (chainFiber S k).card ≤
      if k.2 then
        (shortBoxChain (occupiedRows .first S).card (occupiedRows .second S).card k.1).card
      else
        (longBoxChain (occupiedRows .first S).card (occupiedRows .second S).card k.1).card := by
  classical
  cases hk : k.2
  · apply Finset.card_le_card_of_injOn (vertexRankPoint S)
    · intro v hv
      simpa [hk] using chainFiber_rankPoint_mem hab hv
    · intro v hv w hw h
      exact vertexRankPoint_injective S h
  · apply Finset.card_le_card_of_injOn (vertexRankPoint S)
    · intro v hv
      simpa [hk] using chainFiber_rankPoint_mem hab hv
    · intro v hv w hw h
      exact vertexRankPoint_injective S h

private theorem chainFiber_card_le_diagonalRows
    (S : Finset Vertex) (k : ℕ × Bool)
    (hab : (occupiedRows .first S).card ≤ (occupiedRows .second S).card) :
    (chainFiber S k).card ≤ (occupiedRows .diagonal S).card := by
  classical
  have hinj : Set.InjOn (rowLabel .diagonal S) (chainFiber S k) := by
    intro v hv w hw hlabel
    have hkeyv := chainFiber_key hv
    have hkeyw := chainFiber_key hw
    have ht : vertexChainIndex S v = vertexChainIndex S w := by
      have hvf := congrArg Prod.fst hkeyv
      have hwf := congrArg Prod.fst hkeyw
      exact hvf.trans hwf.symm
    have hdiag : rowCoord .diagonal v = rowCoord .diagonal w := by
      exact congrArg Subtype.val hlabel
    have hvchain := chainFiber_rankPoint_mem hab hv
    have hwchain := chainFiber_rankPoint_mem hab hw
    cases hk : k.2
    · exact diagonal_injective_on_longChain S v w hab ht
        (by simpa [hk] using hvchain) (by simpa [hk] using hwchain) hdiag
    · exact diagonal_injective_on_shortChain S v w ht
        (by simpa [hk] using hvchain) (by simpa [hk] using hwchain) hdiag
  have hcard := Finset.card_le_card_of_injOn (rowLabel .diagonal S)
    (t := (Finset.univ : Finset ↥(occupiedRows .diagonal S)))
    (fun _ _ => Finset.mem_univ _) hinj
  simpa using hcard

private theorem chainFiber_card_le_capacity
    (S : Finset Vertex) (k : ℕ × Bool)
    (hab : (occupiedRows .first S).card ≤ (occupiedRows .second S).card) :
    (chainFiber S k).card ≤
      min (occupiedRows .diagonal S).card
        (if k.2 then
          (shortBoxChain (occupiedRows .first S).card (occupiedRows .second S).card k.1).card
        else
          (longBoxChain (occupiedRows .first S).card (occupiedRows .second S).card k.1).card) := by
  exact le_min (chainFiber_card_le_diagonalRows S k hab)
    (chainFiber_card_le_boxChain S k hab)

/-- Cardinality bound obtained by summing capacities of the symmetric chains. -/
theorem card_le_chainCapSum (S : Finset Vertex)
    (hab : (occupiedRows .first S).card ≤ (occupiedRows .second S).card) :
    S.card ≤ chainCapSum (occupiedRows .first S).card
      (occupiedRows .second S).card (occupiedRows .diagonal S).card := by
  classical
  rw [card_eq_sum_chainFiber]
  calc
    (∑ k ∈ chainKeys S, (chainFiber S k).card) ≤
        ∑ k ∈ chainKeys S,
          min (occupiedRows .diagonal S).card
            (if k.2 then
              (shortBoxChain (occupiedRows .first S).card
                (occupiedRows .second S).card k.1).card
            else
              (longBoxChain (occupiedRows .first S).card
                (occupiedRows .second S).card k.1).card) := by
          exact Finset.sum_le_sum fun k _ => chainFiber_card_le_capacity S k hab
    _ = chainCapSum (occupiedRows .first S).card
        (occupiedRows .second S).card (occupiedRows .diagonal S).card := by
      unfold chainKeys chainCapSum
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro t ht
      have hta : t < (occupiedRows .first S).card := Finset.mem_range.mp ht
      simp [card_longBoxChain _ _ _ hta hab, card_shortBoxChain _ _ _ hta hab,
        add_comm]

end OeisA263135
