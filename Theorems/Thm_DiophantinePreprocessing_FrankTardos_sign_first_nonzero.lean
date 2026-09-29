import Mathlib
import Definitions.Def_DiophantinePreprocessing_FrankTardos_CondIII

namespace DiophantinePreprocessing.FrankTardos

/-- Frank–Tardos, Lemma 3.2 (pp. 54–55): for a decomposition `w = ∑_{i=1}^k λ_i v_i` with
`λ_i > 0`, integer `v_i` and condition (iii), and an integer `b` with `‖b‖₁ ≤ N - 1`,
`sign (b · w) = sign (b · v_j)` for the smallest `j` with `b · v_j ≠ 0`, and `b · w = 0`
if `b · v_i = 0` for every `i`. -/
theorem sign_first_nonzero (n N k : ℕ) (hN : 1 ≤ N) (w : Fin n → ℝ)
    (v : ℕ → Fin n → ℤ) (lam : ℕ → ℝ)
    (hlam : ∀ i ∈ Finset.Icc 1 k, 0 < lam i)
    (hw : ∀ l, w l = ∑ i ∈ Finset.Icc 1 k, lam i * (v i l : ℝ))
    (hIII : CondIII N k lam v)
    (b : Fin n → ℤ) (hb : ∑ l, |b l| ≤ (N : ℤ) - 1) :
    (∀ j ∈ Finset.Icc 1 k,
        (∀ i ∈ Finset.Ico 1 j, ∑ l, b l * v i l = 0) → ∑ l, b l * v j l ≠ 0 →
        SignType.sign (∑ l, (b l : ℝ) * w l) = SignType.sign ((∑ l, b l * v j l : ℤ) : ℝ)) ∧
    ((∀ i ∈ Finset.Icc 1 k, ∑ l, b l * v i l = 0) → ∑ l, (b l : ℝ) * w l = 0) := by sorry

end DiophantinePreprocessing.FrankTardos
