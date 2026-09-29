import Mathlib
import Definitions.Def_TSPHeuristics_NNLower_ShortestPathMetric

namespace TSPHeuristics.NNLower

/-- The edge length `l_i` of eq. (2.11), p. 567: `l_i = (1/6)(4 · 2^i − (−1)^i + 3)`. -/
noncomputable def ell (i : ℕ) : ℝ := (4 * 2 ^ i - (-1) ^ i + 3) / 6

/-- The number of nodes of `F_i` (and of `G_i`, `Ḡ_i`): `2^(i+1) − 1`. -/
def numNodes (i : ℕ) : ℕ := 2 ^ (i + 1) - 1

/-- The position of the middle node of `F_i`: `2^i − 1`. The start node is `0` and the right
node is `numNodes i − 1`; the nodes of `F_i` are `0, 1, …, numNodes i − 1`, left to right. -/
def middle (i : ℕ) : ℕ := 2 ^ i - 1

/-- The edges of the incomplete weighted graph `F_i` (pp. 567, Fig. 1), for `i ≥ 1`, as triples
(endpoint, endpoint, weight). `F_1` is a triangle with all weights `1`. `F_{i+1}` consists of the
left copy of `F_i` (nodes `0 … s − 1`, `s = numNodes i`), the new node `D = s`, and the right copy
of `F_i` shifted by `s + 1`, plus the edges `(C, D)` and `(D, E)` of length `1`, `(D, F)` and
`(B, E)` of length `l_i`, where `B = middle i`, `C = s − 1`, `E = s + 1`, `F = s + 1 + middle i`.
The value at `i = 0` is a placeholder (`F_0` is not defined in the paper). -/
noncomputable def edgesF : ℕ → List (ℕ × ℕ × ℝ)
  | 0 => []
  | 1 => [(0, 1, 1), (1, 2, 1), (0, 2, 1)]
  | i + 2 =>
    edgesF (i + 1) ++
      (edgesF (i + 1)).map (fun e => (e.1 + (numNodes (i + 1) + 1), e.2.1 + (numNodes (i + 1) + 1), e.2.2)) ++
      [(numNodes (i + 1) - 1, numNodes (i + 1), 1),
       (numNodes (i + 1), numNodes (i + 1) + 1, 1),
       (numNodes (i + 1), numNodes (i + 1) + 1 + middle (i + 1), ell (i + 1)),
       (middle (i + 1), numNodes (i + 1) + 1, ell (i + 1))]

/-- The path `P_i` of `F_i` (p. 567), as the list of nodes it visits from the start node to the
middle node: `P_1 = [start, right, middle] = [0, 2, 1]`; `P_{i+1}` is `P_i` in the left copy, the
edge `(B, E)`, `P_i` in the right copy, and the edge `(F, D)`. -/
def pathP : ℕ → List ℕ
  | 0 => []
  | 1 => [0, 2, 1]
  | i + 2 => pathP (i + 1) ++ (pathP (i + 1)).map (· + (numNodes (i + 1) + 1)) ++ [numNodes (i + 1)]

/-- The length `L_i` of the path `P_i`, given by the difference equation of p. 567:
`L_1 = 2`, `L_{i+1} = 2 · L_i + 2 · l_i`. The value at `i = 0` is a placeholder. -/
noncomputable def pathLength : ℕ → ℝ
  | 0 => 0
  | 1 => 2
  | i + 2 => 2 * pathLength (i + 1) + 2 * ell (i + 1)

/-- The edges of `G_i` (p. 568): the edges of `F_i` plus an edge of length `1` between the start
node and the right node and an edge of length `l_i − 1` between the middle node and the start
node. -/
noncomputable def edgesG (i : ℕ) : List (ℕ × ℕ × ℝ) :=
  edgesF i ++ [(0, numNodes i - 1, 1), (middle i, 0, ell i - 1)]

/-- The complete graph `Ḡ_i` (p. 568) on the nodes of `G_i`: `d(a, b)` is the length of a minimal
path from `a` to `b` in `G_i`. -/
noncomputable def gbar (i : ℕ) : Fin (numNodes i) → Fin (numNodes i) → ℝ :=
  fun a b => spDist (edgesG i) a b

end TSPHeuristics.NNLower
