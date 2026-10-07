import Mathlib
import Definitions.Def_SolomonRWRE_DiffEq_System

open MeasureTheory ProbabilityTheory

namespace SolomonRWRE.DiffEq

/-- **The two-sided i.i.d. family** of the proof of Theorem (4.4), p. 29: "Without loss of
generality we may assume that `σ_j` is the `j`th coordinate function on the probability space
`([0, ∞]^Z, 𝓕, P)` … and `P` is the product measure."

**Formalization Note.** This is a different object from `IsIIDNonneg`: the family is indexed
by `ℤ`, and all of `σ_j`, `j ∈ ℤ`, are independent, nonnegative and identically distributed.
The values are real (the paper's `[0, ∞]` coordinates take the value `∞` with probability `0`).
`Z` is applied to its restriction `n ↦ σ n` to `ℕ`, which uses `σ_1, …, σ_n` only. -/
structure IsIIDNonnegZ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (σ : ℤ → Ω → ℝ) :
    Prop where
  meas : ∀ n, Measurable (σ n)
  nonneg : ∀ n ω, 0 ≤ σ n ω
  indep : iIndepFun σ P
  ident : ∀ n, IdentDistrib (σ n) (σ 1) P P

/-- **`S_n = Σ_{j=−∞}^n σ_j ⋯ σ_n`** (proof of Theorem (4.4), p. 29), in `[0, ∞]`.
The term with index `m` is `σ_{n−m} ⋯ σ_n`, i.e. `j = n − m`. -/
noncomputable def S {Ω : Type*} (σ : ℤ → Ω → ℝ) (n : ℤ) (ω : Ω) : ENNReal :=
  ∑' m : ℕ, ∏ l ∈ Finset.range (m + 1), ENNReal.ofReal (σ (n - l) ω)

end SolomonRWRE.DiffEq
