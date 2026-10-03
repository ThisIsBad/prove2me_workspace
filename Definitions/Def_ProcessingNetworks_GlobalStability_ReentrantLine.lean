import Mathlib
import Definitions.Def_ProcessingNetworks_GlobalStability_QueueingNetworkData

namespace ProcessingNetworks.GlobalStability

/-- The two-station, five-class re-entrant queueing network of Figure 8.3, Dai & Harrison p. 155
(PDF p. 171): classes `0,…,4` (standing for the book's classes `1,…,5`) form a single
deterministic route `0 → 1 → 2 → 3 → 4 → exit`, with external arrivals (rate `lam1`) only into
class `0`. Station 1 serves classes `{0,2,4}` (the book's `{1,3,5}`), station 2 serves classes
`{1,3}` (the book's `{2,4}`); both are single-server (`b ≡ 1`). -/
def reentrantLineData (lam1 m1 m2 m3 m4 m5 : ℝ) : QueueingNetworkData 5 2 where
  p := ![0, 1, 0, 1, 0]
  P := fun i j => if (i : ℕ) + 1 = (j : ℕ) then 1 else 0
  m := ![m1, m2, m3, m4, m5]
  lam := ![lam1, 0, 0, 0, 0]
  b := ![1, 1]

/-- `G₁(t) := x₁Z₁⁺(t) + x₃Z₃⁺(t) + x₅Z₅⁺(t)`, Eq. (8.50), where `Zⱼ⁺ := Z₁+⋯+Zⱼ`: the
piecewise-linear Lyapunov function's station-1 component, for the re-entrant line with classes
`0,2,4` (`1,3,5`) at station 1. -/
def reentrantG1 (x1 x3 x5 : ℝ) (Zh : ℝ → Fin 5 → ℝ) (t : ℝ) : ℝ :=
  x1 * Zh t 0 + x3 * (Zh t 0 + Zh t 1 + Zh t 2) + x5 * (Zh t 0 + Zh t 1 + Zh t 2 + Zh t 3 + Zh t 4)

/-- `G₂(t) := x₂Z₂⁺(t) + x₄Z₄⁺(t)`, Eq. (8.51): the station-2 component. -/
def reentrantG2 (x2 x4 : ℝ) (Zh : ℝ → Fin 5 → ℝ) (t : ℝ) : ℝ :=
  x2 * (Zh t 0 + Zh t 1) + x4 * (Zh t 0 + Zh t 1 + Zh t 2 + Zh t 3)

/-- `H₁(t) := Z₁(t)+Z₃(t)+Z₅(t)`: the total fluid at station 1. -/
def reentrantH1 (Zh : ℝ → Fin 5 → ℝ) (t : ℝ) : ℝ :=
  Zh t 0 + Zh t 2 + Zh t 4

/-- `H₂(t) := Z₂(t)+Z₄(t)`: the total fluid at station 2. -/
def reentrantH2 (Zh : ℝ → Fin 5 → ℝ) (t : ℝ) : ℝ :=
  Zh t 1 + Zh t 3

end ProcessingNetworks.GlobalStability
