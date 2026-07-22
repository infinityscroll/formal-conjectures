import FormalConjectures.OEIS.«263135»

namespace OeisA263135

inductive RowKind
  | first
  | second
  | diagonal
  deriving DecidableEq, Fintype

/-- The three integer row coordinates on the honeycomb graph. -/
def rowCoord : RowKind → Vertex → ℤ
  | .first, v => v.i
  | .second, v => v.j
  | .diagonal, v => v.i + v.j + if v.side then 1 else 0

/-- A coordinate increasing by one along consecutive vertices of a fixed row. -/
def alongCoord : RowKind → Vertex → ℤ
  | .first, v => 2 * v.j + if v.side then 1 else 0
  | .second, v => 2 * v.i + if v.side then 1 else 0
  | .diagonal, v => 2 * v.i + if v.side then 1 else 0

/-- The direction from `v` to the predecessor on a row. -/
def prevDirection : RowKind → Vertex → Direction
  | .first, ⟨_, _, false⟩ => .diagonal
  | .first, ⟨_, _, true⟩ => .same
  | .second, ⟨_, _, false⟩ => .horizontal
  | .second, ⟨_, _, true⟩ => .same
  | .diagonal, ⟨_, _, false⟩ => .horizontal
  | .diagonal, ⟨_, _, true⟩ => .diagonal

/-- The direction from `v` to the successor on a row. -/
def nextDirection : RowKind → Vertex → Direction
  | .first, ⟨_, _, false⟩ => .same
  | .first, ⟨_, _, true⟩ => .diagonal
  | .second, ⟨_, _, false⟩ => .same
  | .second, ⟨_, _, true⟩ => .horizontal
  | .diagonal, ⟨_, _, false⟩ => .diagonal
  | .diagonal, ⟨_, _, true⟩ => .horizontal

@[simp]
theorem rowCoord_neighbor_prev (r : RowKind) (v : Vertex) :
    rowCoord r (neighbor v (prevDirection r v)) = rowCoord r v := by
  rcases v with ⟨i, j, side⟩
  cases r <;> cases side <;> simp [rowCoord, prevDirection, neighbor]

@[simp]
theorem rowCoord_neighbor_next (r : RowKind) (v : Vertex) :
    rowCoord r (neighbor v (nextDirection r v)) = rowCoord r v := by
  rcases v with ⟨i, j, side⟩
  cases r <;> cases side <;> simp [rowCoord, nextDirection, neighbor]

@[simp]
theorem alongCoord_neighbor_prev (r : RowKind) (v : Vertex) :
    alongCoord r (neighbor v (prevDirection r v)) = alongCoord r v - 1 := by
  rcases v with ⟨i, j, side⟩
  cases r <;> cases side <;> simp [alongCoord, prevDirection, neighbor]

@[simp]
theorem alongCoord_neighbor_next (r : RowKind) (v : Vertex) :
    alongCoord r (neighbor v (nextDirection r v)) = alongCoord r v + 1 := by
  rcases v with ⟨i, j, side⟩
  cases r <;> cases side <;> simp [alongCoord, nextDirection, neighbor]

@[simp]
theorem prevDirection_ne_nextDirection (r : RowKind) (v : Vertex) :
    prevDirection r v ≠ nextDirection r v := by
  rcases v with ⟨i, j, side⟩
  cases r <;> cases side <;> decide

/-- Directed boundary incidences of a finite honeycomb set. -/
def boundaryDarts (S : Finset Vertex) : Finset (Vertex × Direction) :=
  (S ×ˢ Finset.univ).filter fun vd => neighbor vd.1 vd.2 ∉ S

/-- Number of directed edges from `S` to its complement. -/
def edgeBoundary (S : Finset Vertex) : ℕ := (boundaryDarts S).card

/-- The set of row labels occupied by `S` in one of the three directions. -/
def occupiedRows (r : RowKind) (S : Finset Vertex) : Finset ℤ :=
  S.image (rowCoord r)

end OeisA263135
