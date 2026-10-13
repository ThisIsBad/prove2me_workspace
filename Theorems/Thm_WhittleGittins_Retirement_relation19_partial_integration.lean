import Mathlib
import Definitions.Def_WhittleGittins_Retirement_BanditProcess

namespace WhittleGittins.Retirement

open MeasureTheory ProbabilityTheory

/-- Relation (19) (p. 147), partial integration of (13):
`F̂(x, s, M) = φᵢ(xᵢ, sᵢ, M) Pᵢ(x, s, M) + ∫_M^∞ φᵢ(xᵢ, sᵢ, m) d_m Pᵢ(x, s, m)`, the Stieltjes
integral being taken against any Stieltjes function `G` that agrees with `Pᵢ(x, s, ·)`, over
`m > M`. -/
theorem relation19_partial_integration {N : ℕ} {X : Fin N → Type*} [∀ i, MeasurableSpace (X i)]
    (B : BanditProcess N X) (x : ∀ j, X j) (s : Fin N → ℕ) (i : Fin N) (M : ℝ)
    (G : StieltjesFunction ℝ) (hG : ∀ m, G m = Pdist B x s i m) :
    Fhat B x s M = phi B i (x i) (s i) M * Pdist B x s i M +
      ∫ m in Set.Ioi M, phi B i (x i) (s i) m ∂G.measure := by sorry

end WhittleGittins.Retirement

