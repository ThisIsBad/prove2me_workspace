import Mathlib
import Definitions.Def_MultiperiodRisk_Bellman_TestSet
import Definitions.Def_MultiperiodRisk_Bellman_EssInf

namespace MultiperiodRisk.Bellman

open MeasureTheory

variable {Ω : Type*} {m : MeasurableSpace Ω} {P₀ : Measure Ω} {ℱ : Filtration ℕ m} {N : ℕ}

/-- The family `{𝐄_ℚ[X_τ | ℱ_σ] | τ ≥ σ a stopping time (bounded by N), ℚ ∈ 𝒫ᵉ}`. -/
def psiFamily (D : TestSet P₀ ℱ N) (X : ℕ → Ω → ℝ) (σ : Ω → WithTop ℕ)
    (hσ : IsStoppingTime ℱ σ) : Set (Ω → ℝ) :=
  {h | ∃ τ : Ω → WithTop ℕ, IsBddStoppingTime ℱ N τ ∧ (∀ ω, σ ω ≤ τ ω) ∧
    ∃ f ∈ Pe D, h = (Q P₀ f)[stoppedValue X τ | hσ.measurableSpace]}

/-- Theorem 4.2: `Ψ_σ(X) = ess.inf {𝐄_ℚ[X_τ | ℱ_σ] | τ ≥ σ, ℚ ∈ 𝒫ᵉ}`, the essential
infimum being taken `P₀`-a.s. among `ℱ_σ`-measurable functions. -/
noncomputable def Psi (D : TestSet P₀ ℱ N) (X : ℕ → Ω → ℝ) (σ : Ω → WithTop ℕ)
    (hσ : IsStoppingTime ℱ σ) : Ω → ℝ :=
  essInfFamily P₀ hσ.measurableSpace (psiFamily D X σ hσ)

/-- The process `n ↦ Ψ_n(X)`: `Ψ` at the constant stopping time `n` (read for `n ≤ N`). -/
noncomputable def PsiN (D : TestSet P₀ ℱ N) (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  Psi D X (fun _ => (n : WithTop ℕ)) (isStoppingTime_const ℱ (n : ℕ))

/-- Backward recursion of Theorem 4.1, indexed by `k = N - n`:
`psiBarAux 0 = X_N`, and `psiBarAux (k+1) = X_{N-k-1} ∧ ess.inf_{ℚ∈𝒫ᵉ} 𝐄_ℚ[psiBarAux k | ℱ_{N-k-1}]`. -/
noncomputable def psiBarAux (D : TestSet P₀ ℱ N) (X : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => X N
  | k + 1 => fun ω => min (X (N - (k + 1)) ω)
      (essInfFamily P₀ (ℱ (N - (k + 1)))
        {h | ∃ f ∈ Pe D, h = (Q P₀ f)[psiBarAux D X k | ℱ (N - (k + 1))]} ω)

/-- Theorem 4.1: the generalized Snell envelope `Ψ̄(X)`, with `Ψ̄_N(X) = X_N` and
`Ψ̄_n(X) = X_n ∧ ess.inf_{ℚ∈𝒫ᵉ} 𝐄_ℚ[Ψ̄_{n+1}(X) | ℱ_n]` for `0 ≤ n < N`.
For `n > N` the value is frozen at `X_N` (never read). -/
noncomputable def PsiBar (D : TestSet P₀ ℱ N) (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  if n ≤ N then psiBarAux D X (N - n) else X N

end MultiperiodRisk.Bellman
