import Mathlib
import Definitions.Def_RobustLS_Structured_Core

open Matrix

namespace RobustLS.Structured

/-- **Lemma 2.1 (S-procedure), sufficiency, every p** — El Ghaoui & Lebret, Robust Solutions to
Least-Squares Problems with Uncertain Data, SIAM J. Matrix Anal. Appl. 18(4) (1997), §2.2,
p. 1038 (PDF p. 4). Let `Fᵢ(ζ) = ζᵀTᵢζ + 2uᵢᵀζ + vᵢ` (`i = 0, …, p`) with `Tᵢ = Tᵢᵀ`. If there
exist `τ₁, …, τ_p ≥ 0` with `[T₀ u₀; u₀ᵀ v₀] − ∑ τᵢ [Tᵢ uᵢ; uᵢᵀ vᵢ] ⪰ 0`, then `F₀(ζ) ≥ 0` for
every `ζ` with `Fᵢ(ζ) ≥ 0` for all `i = 1, …, p`. The family `F₁, …, F_p` is indexed by
`Fin p` (`T i` is the paper's `T_{i+1}`). -/
theorem s_procedure_sufficient {m p : ℕ} (T0 : Matrix (Fin m) (Fin m) ℝ) (u0 : Fin m → ℝ)
    (v0 : ℝ) (T : Fin p → Matrix (Fin m) (Fin m) ℝ) (u : Fin p → Fin m → ℝ) (v : Fin p → ℝ)
    (hT0 : T0ᵀ = T0) (hT : ∀ i, (T i)ᵀ = T i)
    (hτ : ∃ τ : Fin p → ℝ, (∀ i, 0 ≤ τ i) ∧
      (quadBlockMat T0 u0 v0 - ∑ i, τ i • quadBlockMat (T i) (u i) (v i)).PosSemidef) :
    ∀ ζ : Fin m → ℝ, (∀ i, 0 ≤ quadFn (T i) (u i) (v i) ζ) → 0 ≤ quadFn T0 u0 v0 ζ := by sorry

end RobustLS.Structured
