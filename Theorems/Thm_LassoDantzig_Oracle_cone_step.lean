import Mathlib
import Definitions.Def_LassoDantzig_Oracle_Model

open MeasureTheory ProbabilityTheory

namespace LassoDantzig.Oracle

/-- **Cone step in the proof of Theorem 6.1** (p. 26, first display). On the event `𝒜`, for
every Lasso solution `β̂` with tuning constant `r > 0` and every `β` in case (B.24),
`ε‖f_β − f‖_n² < 4r|δ_{J₀}|_1`, where `δ = D^{1/2}(β̂ − β)` (so `|δ_j| = ‖f_j‖_n |β̂_j − β_j|`) and
`J₀ = J(β)`: `|δ|_1 ≤ 4(1 + 1/ε)|δ_{J₀}|_1`, hence `|δ_{J₀ᶜ}|_1 ≤ (3 + 4/ε)|δ_{J₀}|_1`, and the
unweighted `δ' = β̂ − β` satisfies `|δ'_{J₀ᶜ}|_1 ≤ (3 + 4/ε)(f_max/f_min)|δ'_{J₀}|_1`. -/
theorem cone_step {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M) (X : Matrix (Fin n) (Fin M) ℝ)
    (hcol : ∀ j, colNorm X j ≠ 0) (f y : Fin n → ℝ) (r : ℝ) (hr : 0 < r)
    (hA : NoiseBound X (fun i => y i - f i) r) (ε : ℝ) (hε : 0 < ε)
    (βhat : Fin M → ℝ) (hL : IsLasso X y r βhat) (β : Fin M → ℝ)
    (hB24 : ε * empSq (fun i => X.mulVec β i - f i) <
      4 * r * ∑ j ∈ supp β, colNorm X j * |βhat j - β j|) :
    ∑ j, colNorm X j * |βhat j - β j| ≤
        4 * (1 + 1 / ε) * ∑ j ∈ supp β, colNorm X j * |βhat j - β j| ∧
      ∑ j ∈ (supp β)ᶜ, colNorm X j * |βhat j - β j| ≤
        (3 + 4 / ε) * ∑ j ∈ supp β, colNorm X j * |βhat j - β j| ∧
      ConeCond ((3 + 4 / ε) * fmax X / fmin X) (supp β) (βhat - β) := by sorry

end LassoDantzig.Oracle
