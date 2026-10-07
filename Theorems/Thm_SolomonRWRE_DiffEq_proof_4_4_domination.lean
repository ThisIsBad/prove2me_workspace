import Mathlib
import Definitions.Def_SolomonRWRE_DiffEq_System
import Definitions.Def_SolomonRWRE_DiffEq_TwoSided

open MeasureTheory ProbabilityTheory Filter Topology

namespace SolomonRWRE.DiffEq

/-- **Proof of Theorem (4.4), p. 29** (unnumbered): for a two-sided i.i.d. nonnegative family
`{σ_j}_{j ∈ ℤ}`, `Z_n(σ) = Σ_{j=1}^n σ_j ⋯ σ_n ≤ Σ_{j=−∞}^n σ_j ⋯ σ_n = S_n(σ)`, and
"`S_n` is finite a.e. since `ν < 1`".

**Formalization Note.** This is stated for the `ℤ`-indexed family `IsIIDNonnegZ` (the page's
"without loss of generality" coordinate model), not for the `ℕ`-indexed family of the goal;
`Z` is computed from its restriction to `ℕ` (it uses `σ_1, …, σ_n` only), and
`ν = E(σ_1)` is `nu` of that restriction. The comparison is pathwise in `[0, ∞]`
(`Z_n ≥ 0` there); the finiteness is for every `n ∈ ℤ`. -/
theorem proof_4_4_domination {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (σ : ℤ → Ω → ℝ) (hσ : IsIIDNonnegZ P σ) :
    (∀ (n : ℕ) (ω : Ω), ENNReal.ofReal (Z (fun m : ℕ => σ m) n ω) ≤ S σ n ω) ∧
    (nu P (fun m : ℕ => σ m) < 1 → ∀ n : ℤ, ∀ᵐ ω ∂P, S σ n ω < ⊤) := by sorry

end SolomonRWRE.DiffEq

