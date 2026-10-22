import Mathlib
import Definitions.Def_FuzzyExtractors_LowerBound_Basic

namespace FuzzyExtractors.LowerBound

/-- Lemma C.1, second sentence (Appendix C, p. 40): when `m = log |𝓜|`, an (𝓜, m, m', t)-secure
sketch has `m' ≤ log K(𝓜, t)`. -/
theorem lemma_C_1_uniform {M V : Type} [Fintype M] [Nonempty M] (dis : M → M → ℕ)
    (hzero : ∀ x y, dis x y = 0 ↔ x = y)
    (hsymm : ∀ x y, dis x y = dis y x)
    (htri : ∀ x y z, dis x z ≤ dis x y + dis y z)
    (m m' : ℝ) (t : ℕ)
    (SS : M → PMF V) (Rec : M → V → PMF M) (hSS : FuzzyExtractors.Hamming.IsSecureSketch dis m m' t SS Rec)
    (hm : m = Real.logb 2 (Fintype.card M)) :
    m' ≤ Real.logb 2 (K dis t Finset.univ) := by sorry

end FuzzyExtractors.LowerBound

