import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_SpectralProjGrad_Shared_scaledProjGrad

namespace SpectralProjGrad.SPG1

/-- Lemma 2.2 (ii): for every `x ∈ Ω` there is `s_x > 0` such that for all `t ∈ [0, s_x]`,
`f(P(x - t g(x))) - f(x) ≤ γ ⟨g(x), g_t(x)⟩`, where `g_t(x) = P(x - t g(x)) - x`
(at `t = 0` the same formula gives `g_0(x) = P(x) - x`). -/
theorem armijo_along_projection_arc {n : ℕ}
    {Ω U : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {γ : ℝ}
    (hΩ_closed : IsClosed Ω) (hΩ_convex : Convex ℝ Ω)
    (hU_open : IsOpen U) (hΩU : Ω ⊆ U) (hf : ContDiffOn ℝ 1 f U)
    (hP : SpectralProjGrad.Shared.IsProjOnto Ω P)
    (hγ : γ ∈ Set.Ioo 0 1)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Ω) :
    ∃ sx : ℝ, 0 < sx ∧ ∀ t ∈ Set.Icc 0 sx,
      f (P (x - t • gradient f x)) - f x ≤ γ * inner ℝ (gradient f x) (SpectralProjGrad.Shared.scaledProjGrad P f t x) := by sorry

end SpectralProjGrad.SPG1

