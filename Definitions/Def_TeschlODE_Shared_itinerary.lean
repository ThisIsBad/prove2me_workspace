import Mathlib
import Definitions.Def_TeschlODE_Shared_tentMap

namespace TeschlODE.Shared

/-- Teschl, §11.4, p. 300, (11.23): the itinerary map `ϕ : Λ → Σ₂`, `ϕ(x)ₙ = j` if
`T_µⁿ(x) ∈ I_j`, where `I₀ = [0, 1/µ]` and `I₁ = [1 − 1/µ, 1]`. For `µ > 2` and `x ∈ Λ` every
iterate lies in `Λ ⊆ I₀ ∪ I₁` and `I₀ ∩ I₁ = ∅`, so `ϕ(x)ₙ = 0` iff `T_µⁿ(x) ∈ I₀`, which is how it
is written here. Values at points outside `Λ` carry no meaning. -/
noncomputable def itinerary (μ : ℝ) (x : ℝ) : ℕ → Fin 2 :=
  fun n => if (tentMap μ)^[n] x ∈ Set.Icc (0 : ℝ) (1 / μ) then 0 else 1

end TeschlODE.Shared
