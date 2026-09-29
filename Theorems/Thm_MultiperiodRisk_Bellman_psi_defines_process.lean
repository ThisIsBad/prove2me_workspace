import Mathlib
import Definitions.Def_MultiperiodRisk_Bellman_Psi

namespace MultiperiodRisk.Bellman

open MeasureTheory

/-- Theorem 4.2, first sentence: the family `(Ψ_σ(X))_σ` defines a process, i.e. the value
at a stopping time `σ` is the process `n ↦ Ψ_n(X)` evaluated at time `σ(ω)`. -/
theorem psi_defines_process {Ω : Type*} {m : MeasurableSpace Ω} (P₀ : Measure Ω)
    [IsProbabilityMeasure P₀] (ℱ : Filtration ℕ m) (N : ℕ) (D : TestSet P₀ ℱ N)
    (hPe : (Pe D).Nonempty) (X : ℕ → Ω → ℝ) (hX : IsValueProcess P₀ ℱ N X)
    (σ : Ω → WithTop ℕ) (hσ : IsBddStoppingTime ℱ N σ) :
    Psi D X σ hσ.1 =ᵐ[P₀] fun ω =>
      ∑ t ∈ Finset.range (N + 1), if σ ω = (t : WithTop ℕ) then PsiN D X t ω else 0 := by sorry

end MultiperiodRisk.Bellman
