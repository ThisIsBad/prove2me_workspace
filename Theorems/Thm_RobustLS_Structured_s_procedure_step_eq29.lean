import Mathlib
import Definitions.Def_RobustLS_Structured_Core

open Matrix

namespace RobustLS.Structured

/-- **The S-procedure step, Eq. (29)** — El Ghaoui & Lebret (1997), §4.1, pp. 1044–1045
(PDF pp. 10–11). Let `λ ≥ 0` and `F, g, h` as in (27). Then
`[1; δ]ᵀ [h gᵀ; g F] [1; δ] ≤ λ` for every `δ` with `δᵀδ ≤ 1` if and only if there is a scalar
`τ` with `𝓕(λ, τ) = [λ − τ − h, −gᵀ; −g, τI − F] ⪰ 0`.
The hypothesis `1 ≤ p` is not written in the paper but is needed: for `p = 0` the block `τI − F`
is empty, `τ` is unconstrained and (29) holds for every `λ` (take `τ` very negative). -/
theorem s_procedure_step_eq29 {n m p : ℕ} (hp : 1 ≤ p) (A0 : Matrix (Fin n) (Fin m) ℝ)
    (A : Fin p → Matrix (Fin n) (Fin m) ℝ) (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ)
    (x : Fin m → ℝ) (lam : ℝ) (hlam : 0 ≤ lam) :
    (∀ δ : Fin p → ℝ, δ ⬝ᵥ δ ≤ 1 → oneStack δ ⬝ᵥ (hgFBlock A0 A b0 b x *ᵥ oneStack δ) ≤ lam) ↔
      ∃ τ : ℝ, (calF A0 A b0 b x lam τ).PosSemidef := by sorry

end RobustLS.Structured
