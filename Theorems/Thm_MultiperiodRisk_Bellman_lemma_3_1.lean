import Mathlib
import Definitions.Def_MultiperiodRisk_Bellman_TestSet

namespace MultiperiodRisk.Bellman

open MeasureTheory

/-- Lemma 3.1: for a stable set and stopping times `τ ≤ σ ≤ ν`,
`{(Z_ν/Z_σ, Z_σ/Z_τ) | Z ∈ 𝒫ᵉ} = {(Z'_ν/Z'_σ, Z_σ/Z_τ) | Z, Z' ∈ 𝒫ᵉ}`, as sets of
`P₀`-a.e. classes of pairs. -/
theorem lemma_3_1 {Ω : Type*} {m : MeasurableSpace Ω} (P₀ : Measure Ω)
    [IsProbabilityMeasure P₀] (ℱ : Filtration ℕ m) (N : ℕ) (D : TestSet P₀ ℱ N)
    (hstab : IsStable D) (τ σ ν : Ω → WithTop ℕ) (hτ : IsBddStoppingTime ℱ N τ)
    (hσ : IsBddStoppingTime ℱ N σ) (hν : IsBddStoppingTime ℱ N ν)
    (hτσ : ∀ ω, τ ω ≤ σ ω) (hσν : ∀ ω, σ ω ≤ ν ω) :
    (∀ f ∈ Pe D, ∃ g ∈ Pe D, ∃ g' ∈ Pe D,
      (fun ω => stoppedValue (Z P₀ ℱ f) ν ω / stoppedValue (Z P₀ ℱ f) σ ω) =ᵐ[P₀]
        (fun ω => stoppedValue (Z P₀ ℱ g') ν ω / stoppedValue (Z P₀ ℱ g') σ ω) ∧
      (fun ω => stoppedValue (Z P₀ ℱ f) σ ω / stoppedValue (Z P₀ ℱ f) τ ω) =ᵐ[P₀]
        (fun ω => stoppedValue (Z P₀ ℱ g) σ ω / stoppedValue (Z P₀ ℱ g) τ ω)) ∧
    (∀ f ∈ Pe D, ∀ f' ∈ Pe D, ∃ g ∈ Pe D,
      (fun ω => stoppedValue (Z P₀ ℱ g) ν ω / stoppedValue (Z P₀ ℱ g) σ ω) =ᵐ[P₀]
        (fun ω => stoppedValue (Z P₀ ℱ f') ν ω / stoppedValue (Z P₀ ℱ f') σ ω) ∧
      (fun ω => stoppedValue (Z P₀ ℱ g) σ ω / stoppedValue (Z P₀ ℱ g) τ ω) =ᵐ[P₀]
        (fun ω => stoppedValue (Z P₀ ℱ f) σ ω / stoppedValue (Z P₀ ℱ f) τ ω)) := by sorry

end MultiperiodRisk.Bellman
