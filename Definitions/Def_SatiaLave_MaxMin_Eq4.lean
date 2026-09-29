import Mathlib
import Definitions.Def_SatiaLave_MaxMin_Model

namespace SatiaLave.MaxMin

open Finset MeasureTheory

variable {S : Type*} [Fintype S] [DecidableEq S] {D : S → Type*} [∀ i, Fintype (D i)]

/-- The right-hand side of the dynamic-programming equations (4) (Satia–Lave 1973, p. 730,
Proposition 1), evaluated at a value vector `v` in state `j`: the supremum over randomized
decisions `τ` (a probability vector on the decisions `D j`) of
`Σ_k τ_k · inf_α ∫ Σ_l p_l (r^k_jl + β v_l) dα(p)`, where the infimum runs over all
probability measures `α` on row vectors that are carried by the uncertainty set `S_j^k`. -/
noncomputable def eq4Op (M : UncertainMDP S D) (v : S → ℝ) (j : S) : ℝ :=
  ⨆ τ : stdSimplex ℝ (D j), ∑ k, (τ : D j → ℝ) k *
    ⨅ α : {μ : ProbabilityMeasure (S → ℝ) // (μ : Measure (S → ℝ)) (M.U j k) = 1},
      ∫ p, ∑ l, p l * (M.r j k l + M.β * v l) ∂(α.1 : Measure (S → ℝ))

end SatiaLave.MaxMin
