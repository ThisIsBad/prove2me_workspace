import Mathlib
import Definitions.Def_HoffmanBound_ErrorBound_Model

namespace HoffmanBound.ErrorBound

open Matrix

/-- Hoffman 1952, p. 263, Lemma 3. Let `M` be obtained from `A` by substituting `0` for the rows
not in `S`, `Ω = {z | M z ≤ 0}`, and `E` the set of `x ∉ Ω` whose nearest point in `Ω` is the
origin. For `F_n`, `F_m` satisfying (3) there is `d_S > 0` with `F_m((M x)⁺) ≥ d_S F_n(x)` for all
`x ∈ E`. -/
theorem lemma3 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin m))
    (Fn : (Fin n → ℝ) → ℝ) (Fm : (Fin m → ℝ) → ℝ)
    (hFn : IsPosHomogeneous Fn) (hFm : IsPosHomogeneous Fm) :
    ∃ dS : ℝ, 0 < dS ∧ ∀ x ∈ setE A S, dS * Fn x ≤ Fm (posPartVec (rowsOn A S *ᵥ x)) := by sorry

end HoffmanBound.ErrorBound

