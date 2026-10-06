import Mathlib
import Definitions.Def_PriceOfStability_Harmonic_Model

open CongestionPoA.AsymSum

namespace PriceOfStability.Harmonic

/-- The edges of the graph of Fig. 1.1 (Anshelevich et al., SIAM J. Comput. 38 (2008), p. 1604
(PDF p. 3)) with `k` players: player `i`'s own edge `s → tᵢ` (`own i`), the common edge from `s`
to the unlabelled bottom node `v` (`common`), and the edge `v → tᵢ` (`zero i`).
Player `i : Fin k` is the paper's player `i + 1`. -/
inductive Fig11Edge (k : ℕ) where
  | own (i : Fin k)
  | common
  | zero (i : Fin k)
  deriving DecidableEq, Fintype

/-- The edge costs of Fig. 1.1 (p. 1604): the own edge of the paper's player `i + 1` costs
`1/(i+1)`, the common edge costs `1 + ε`, and every edge `v → tᵢ` costs `0`. -/
noncomputable def fig11Cost (k : ℕ) (ε : ℝ) : Fig11Edge k → ℝ
  | .own i => 1 / ((i : ℕ) + 1 : ℝ)
  | .common => 1 + ε
  | .zero _ => 0

/-- The two `s`–`tᵢ` paths of player `i` in Fig. 1.1: its own edge, or the common edge followed
by its zero-cost edge `v → tᵢ`. -/
def fig11Strategies (k : ℕ) (i : Fin k) : Finset (Finset (Fig11Edge k)) :=
  {{Fig11Edge.own i}, {Fig11Edge.common, Fig11Edge.zero i}}

/-- The instance of Fig. 1.1 (p. 1604 (PDF p. 3)) as a fair (Shapley) cost-sharing game with
`k` players and constant edge costs `fig11Cost k ε`. -/
noncomputable def fig11 (k : ℕ) (ε : ℝ) : CongestionGame (Fin k) (Fig11Edge k) :=
  fairGame (fig11Strategies k) (fun e _ => fig11Cost k ε e)

end PriceOfStability.Harmonic
