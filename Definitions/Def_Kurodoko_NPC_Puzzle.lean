import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding

namespace Kurodoko.NPC

open CookPvsNP ProjSchedTW.Complexity

/-! # Kurodoko instances, the four rules, and the Kurodoko language (Kölker 2012, §1, p. 694)

A board of width `w` (columns) and height `h` (rows) has the squares `(r, c)` with row `r < h` and
column `c < w`. A clue is a triple `(r, c, n)`: the square `(r, c)` carries the number `n`. -/

/-- A square of the grid, written `(r, c)`: row `r`, column `c` (0-based). -/
abbrev Cell : Type := ℕ × ℕ

/-- The square `v = (r, c)` lies on the board of width `w` and height `h`: `r < h` and `c < w`. -/
def OnBoard (w h : ℕ) (v : Cell) : Prop := v.1 < h ∧ v.2 < w

instance (w h : ℕ) (v : Cell) : Decidable (OnBoard w h v) := by
  unfold OnBoard; infer_instance

/-- Two squares are adjacent iff they are horizontally or vertically adjacent,
`|r − r'| + |c − c'| = 1` (p. 694), stated without subtraction. -/
def Adj (u v : Cell) : Prop :=
  (u.1 = v.1 ∧ (u.2 + 1 = v.2 ∨ v.2 + 1 = u.2)) ∨
    (u.2 = v.2 ∧ (u.1 + 1 = v.1 ∨ v.1 + 1 = u.1))

/-- With the set `B` of black squares, `v` is a white square: it is on the board and not black. -/
def White (w h : ℕ) (B : Finset Cell) (v : Cell) : Prop := OnBoard w h v ∧ v ∉ B

/-- The squares of `v`'s row that `v` touches: the on-board squares `u = (r, c')` of `v`'s row
such that no square from `v` to `u` (inclusive) is black. -/
def rowTouched (w : ℕ) (B : Finset Cell) (v : Cell) : Finset Cell :=
  ((Finset.range w).filter fun c =>
      ∀ c' ∈ Finset.Icc (min v.2 c) (max v.2 c), (v.1, c') ∉ B).image fun c => (v.1, c)

/-- The squares of `v`'s column that `v` touches: the on-board squares `u = (r', c)` of `v`'s
column such that no square from `v` to `u` (inclusive) is black. -/
def colTouched (h : ℕ) (B : Finset Cell) (v : Cell) : Finset Cell :=
  ((Finset.range h).filter fun r =>
      ∀ r' ∈ Finset.Icc (min v.1 r) (max v.1 r), (r', v.2) ∉ B).image fun r => (r, v.2)

/-- The number of squares that `v` touches (p. 694): the white squares reachable from `v` going
in each of the four compass directions, never off the board nor through a black square, `v`
itself counted once. For a white on-board `v` this is `hz + vt − 1`. -/
def touchCount (w h : ℕ) (B : Finset Cell) (v : Cell) : ℕ :=
  (rowTouched w B v ∪ colTouched h B v).card

/-- Rule (1): the clue squares are all white, `B ∩ C = ∅`. -/
def Rule1 (clues : List (ℕ × ℕ × ℕ)) (B : Finset Cell) : Prop :=
  ∀ t ∈ clues, (t.1, t.2.1) ∉ B

/-- Rule (2): no two black squares are adjacent, `(B × B) ∩ E = ∅`. -/
def Rule2 (B : Finset Cell) : Prop :=
  ∀ u ∈ B, ∀ v ∈ B, ¬ Adj u v

/-- Rule (3): all white squares are connected via paths of white squares: any two white squares
are joined by a chain of adjacent white squares (the white set is preconnected). -/
def Rule3 (w h : ℕ) (B : Finset Cell) : Prop :=
  ∀ u v, White w h B u → White w h B v →
    Relation.ReflTransGen (fun a b => Adj a b ∧ White w h B a ∧ White w h B b) u v

/-- Rule (4): the number at each clue square equals the number of squares it touches. -/
def Rule4 (w h : ℕ) (clues : List (ℕ × ℕ × ℕ)) (B : Finset Cell) : Prop :=
  ∀ t ∈ clues, touchCount w h B (t.1, t.2.1) = t.2.2

/-- `B` is a solution of the instance `(w, h, clues)`: a set of squares of the board
(`B ⊆ V`) satisfying rules (1)–(4). -/
def IsSolution (w h : ℕ) (clues : List (ℕ × ℕ × ℕ)) (B : Finset Cell) : Prop :=
  (∀ v ∈ B, OnBoard w h v) ∧ Rule1 clues B ∧ Rule2 B ∧ Rule3 w h B ∧ Rule4 w h clues B

/-- The instance `(w, h, clues)` is well formed (p. 694): every clue square is on the board, no
square carries two clues, and every clue value lies in `{1, …, w + h − 1}`. -/
def WellFormed (w h : ℕ) (clues : List (ℕ × ℕ × ℕ)) : Prop :=
  (∀ t ∈ clues, OnBoard w h (t.1, t.2.1) ∧ 1 ≤ t.2.2 ∧ t.2.2 ≤ w + h - 1) ∧
    (clues.map fun t => (t.1, t.2.1)).Nodup

/-- The instance `(w, h, clues)` has a solution. -/
def Solvable (w h : ℕ) (clues : List (ℕ × ℕ × ℕ)) : Prop :=
  ∃ B : Finset Cell, IsSolution w h clues B

/-- The code of an instance: `w`, `h`, then `r, c, n` for every clue `(r, c, n)` in list order,
every number in binary (`encNats`). -/
def code (w h : ℕ) (clues : List (ℕ × ℕ × ℕ)) : List BSym :=
  encNats ([w, h] ++ clues.flatMap fun t => [t.1, t.2.1, t.2.2])

/-- The Kurodoko Decision Problem as a language: the codes of the well-formed solvable
instances. -/
def kurodokoLang : Lang BSym :=
  { s | ∃ (w h : ℕ) (clues : List (ℕ × ℕ × ℕ)),
      WellFormed w h clues ∧ Solvable w h clues ∧ s = code w h clues }

end Kurodoko.NPC
