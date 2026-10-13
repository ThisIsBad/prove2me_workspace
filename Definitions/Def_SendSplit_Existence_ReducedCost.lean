import Mathlib
import Definitions.Def_SendSplit_Existence_Network

namespace SendSplit.Existence

variable {n : ℕ}

/-- The altered arc cost `c^π_ij(y) = c_ij(y) - (π_i - π_j) y` for a node vector `π ∈ ℝ^n`. -/
def reducedArcCost (c : Fin n → Fin n → ℝ → ℝ) (π : Fin n → ℝ) (i j : Fin n) (y : ℝ) : ℝ :=
  c i j y - (π i - π j) * y

/-- The altered flow cost `c^π(x) = ∑_{(i,j) ∈ A} c^π_ij(x_ij)`. -/
def reducedFlowCost (G : ArcGraph n) (c : Fin n → Fin n → ℝ → ℝ) (π : Fin n → ℝ)
    (x : Fin n → Fin n → ℝ) : ℝ :=
  ∑ p ∈ G.A, reducedArcCost c π p.1 p.2 (x p.1 p.2)

end SendSplit.Existence
