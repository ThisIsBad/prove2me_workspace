import Mathlib
import Definitions.Def_DaiWeissFluid_ThreeBuffer_FluidModel

namespace DaiWeissFluid.ThreeBuffer

/-- Lemma 3.2, p. 121, for an arbitrary reentrant line with `I ≥ 1` stations: let
`G_i(t) = ∑_k c i k * Q_k(t)` with nonnegative coefficients and `G(t) = max_i G_i(t)`. If
(a) `W_i(t) > 0` implies `Ġ_i(t) ≤ -ε_i`, and (b) `W_i(t) = 0` implies `G_i(t) ≤ G_j(t)` for all
`j ≠ i`, then `G` is absolutely continuous and nonnegative on `[0, ∞)`, and at every regular point
`t > 0` of `G, G_1, …, G_I` with `G(t) > 0`, `Ġ(t) ≤ -min_i ε_i`. -/
theorem lemma3_2 {I K : ℕ} (L : ReentrantLine I K) (hm : ∀ k, 0 < L.m k) (hI : 0 < I)
    (Q T : ℝ → Fin K → ℝ) (hsol : L.IsFluidSolution Q T)
    (c : Fin I → Fin K → ℝ) (hc : ∀ i k, 0 ≤ c i k) (ε : Fin I → ℝ) (hε : ∀ i, 0 < ε i)
    (ha : ∀ i t, 0 < t → 0 < L.volume Q i t →
      ∀ d, HasDerivAt (fun s => ∑ k, c i k * Q s k) d t → d ≤ -ε i)
    (hb : ∀ i t, 0 ≤ t → L.volume Q i t = 0 →
      ∀ j, j ≠ i → ∑ k, c i k * Q t k ≤ ∑ k, c j k * Q t k) :
    (∀ a b, 0 ≤ a → a ≤ b →
        AbsolutelyContinuousOnInterval (fun s => ⨆ i, ∑ k, c i k * Q s k) a b) ∧
    (∀ t, 0 ≤ t → 0 ≤ ⨆ i, ∑ k, c i k * Q t k) ∧
    (∀ t, 0 < t → 0 < (⨆ i, ∑ k, c i k * Q t k) →
      (∀ i, DifferentiableAt ℝ (fun s => ∑ k, c i k * Q s k) t) →
      ∀ d, HasDerivAt (fun s => ⨆ i, ∑ k, c i k * Q s k) d t →
        d ≤ -(Finset.univ.inf' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hI⟩⟩) ε)) := by sorry

end DaiWeissFluid.ThreeBuffer

