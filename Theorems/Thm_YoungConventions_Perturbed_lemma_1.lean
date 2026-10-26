import Mathlib
import Definitions.Def_YoungConventions_Perturbed_FiniteChain
import Definitions.Def_YoungConventions_Perturbed_InTree
import Definitions.Def_YoungConventions_Perturbed_RegularPerturbation
import Definitions.Def_YoungConventions_Perturbed_StochasticPotential

open Filter Topology Finset

namespace YoungConventions.Perturbed

/-- Lemma 1 (Young 1993, Econometrica 61:57–84, Appendix, p. 78, PDF p. 23; proof pp. 79–80).

Let `P^ε` (`ε ∈ (0, a]`) be a regular perturbation of the Markov chain `P⁰` on the finite set
`X`, and let `μ^ε` be its stationary distribution. Then `μ⁰ = lim_{ε→0} μ^ε` exists and is a
stationary distribution of `P⁰`. Moreover `μ⁰_x > 0` iff `γ(x) ≤ γ(y)` for all `y ∈ X`, where
`γ` is the potential (9) (`statePotential`).

**Formalization Note.** "Let `μ^ε` be its stationary distribution" is encoded by quantifying over
every family `μ` with `μ ε` stationary for `P ε` for all `ε ∈ (0, a]`; by (6) this distribution
is unique, so this is the paper's reading. The limit is one-sided (`ε → 0⁺`) and pointwise in
`x`, which on the finite `X` is convergence of the vector `μ^ε`. -/
theorem lemma_1 {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (P0 : Matrix X X ℝ) (hP0 : P0 ∈ Matrix.rowStochastic ℝ X)
    (P : ℝ → Matrix X X ℝ) (a : ℝ) (hP : IsRegularPerturbation P0 P a)
    (μ : ℝ → X → ℝ) (hμ : ∀ ε ∈ Set.Ioc 0 a, IsStationaryDist (P ε) (μ ε)) :
    ∃ μ0 : X → ℝ,
      (∀ x, Tendsto (fun ε : ℝ => μ ε x) (𝓝[>] 0) (𝓝 (μ0 x))) ∧
      IsStationaryDist P0 μ0 ∧
      ∀ x, (0 < μ0 x ↔ ∀ y, statePotential P x ≤ statePotential P y) := by sorry

end YoungConventions.Perturbed

