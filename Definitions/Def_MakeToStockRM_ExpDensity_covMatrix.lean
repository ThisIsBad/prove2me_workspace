import Mathlib

namespace MakeToStockRM.ExpDensity

/-- The covariance matrix `Σ = [[σ², σδϱ], [σδϱ, δ²]]` of the diffusion `(𝒳, 𝒴)`, read off from
the generator `Γ` (Caldentey–Wein 2006, p. 865). -/
def covMatrix (σ δ ϱ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![σ ^ 2, σ * δ * ϱ; σ * δ * ϱ, δ ^ 2]

end MakeToStockRM.ExpDensity
