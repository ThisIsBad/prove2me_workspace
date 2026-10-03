import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_BaselineAssumptions

namespace ProcessingNetworks.Stability

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

/-- Proposition 2.3 (SLLN for processing variables), Dai & Harrison, p. 31: under the baseline
stochastic assumptions, for each activity `j`, almost surely the sample means of the first `n`
service times and output vectors converge, `(1/n) ∑_{ℓ<n} vⱼ(ℓ) → mⱼ` and
`(1/n) ∑_{ℓ<n} φⱼ(ℓ) → Γⱼ`, as `n → ∞` (`ℓ = 0, …, n-1` here stands for the book's
`ℓ = 1, …, n`). -/
theorem processing_variable_slln {Ω : Type*} [MeasureSpace Ω] {I J : ℕ} {N0 : Fin J → ℕ}
    {E : Fin I → ℝ → Ω → ℕ} {lam : Fin I → ℝ≥0}
    {v : Fin J → ℕ → Ω → ℝ} {φ : Fin J → ℕ → Ω → Fin I → ℕ}
    {m : Fin J → ℝ} {Γ : Fin J → Fin I → ℝ} {Psi : Fin J → ℕ → Ω → ℝ × (Fin I → ℕ)}
    (h : BaselineAssumptions I J N0 E lam v φ m Γ Psi) (j : Fin J) :
    ℙ {ω | Tendsto (fun n : ℕ => (∑ ℓ ∈ Finset.range n, v j ℓ ω) / n) atTop (nhds (m j)) ∧
           ∀ i : Fin I, Tendsto (fun n : ℕ => (∑ ℓ ∈ Finset.range n, (φ j ℓ ω i : ℝ)) / n)
             atTop (nhds (Γ j i))} = 1 := by sorry

end ProcessingNetworks.Stability
