import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SetCoverThreshold_SetCover_Complexity
import Definitions.Def_NSWApxHard_Reduction_Welfare

namespace NSWApxHard.Reduction

open Finset

/-- A graph on the vertex set `Fin N = {0, …, N-1}`. -/
structure GraphInput where
  N : ℕ
  G : SimpleGraph (Fin N)

/-- `G` is 3-regular: every vertex has exactly three neighbours. -/
def IsCubic {N : ℕ} (G : SimpleGraph (Fin N)) : Prop :=
  ∀ v : Fin N, (G.neighborSet v).ncard = 3

open Classical in
/-- The binary encoding of a graph: `N` by `natBits`, then the `N²` adjacency bits
`[i ~ j]`, row by row. -/
noncomputable def encGraph (I : GraphInput) : List Bool :=
  natBits I.N ++
    (List.ofFn fun i : Fin I.N => List.ofFn fun j : Fin I.N => decide (I.G.Adj i j)).flatten

/-- Yes-instances of Theorem 2.1 (Lee, p. 2): a nonempty 3-regular graph with a vertex cover of
size at most `c_min N`. -/
def vcYes (cmin : ℝ) (I : GraphInput) : Prop :=
  0 < I.N ∧ IsCubic I.G ∧
    ∃ C : Finset (Fin I.N), I.G.IsVertexCover ↑C ∧ (C.card : ℝ) ≤ cmin * I.N

/-- No-instances of Theorem 2.1 (Lee, p. 2): a nonempty 3-regular graph every vertex cover of
which has size at least `c_max N`. -/
def vcNo (cmax : ℝ) (I : GraphInput) : Prop :=
  0 < I.N ∧ IsCubic I.G ∧
    ∀ C : Finset (Fin I.N), I.G.IsVertexCover ↑C → cmax * I.N ≤ (C.card : ℝ)

/-- Theorem 2.1 of Lee (p. 2), due to Chlebík and Chlebíková, as a proposition about the
constants `c_min, c_max`: it is NP-hard to distinguish 3-regular graphs with a vertex cover of
size at most `c_min N` from 3-regular graphs all of whose vertex covers have size at least
`c_max N`. -/
def Theorem21 (cmin cmax : ℝ) : Prop :=
  SetCoverThreshold.SetCover.GapNPHard encGraph (vcYes cmin) (vcNo cmax)

end NSWApxHard.Reduction
