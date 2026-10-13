import Mathlib
import Definitions.Def_BertsekasShreve_BorelFinite_Model
import Definitions.Def_BertsekasShreve_BorelFinite_Policy
import Definitions.Def_BertsekasShreve_BorelFinite_Operators

namespace BertsekasShreve.BorelFinite

open Filter Topology in
/-- **Lemma 8.4** (p. 197). Let `{J_k}` be universally measurable functions `S → R*` and
`μ ∈ U(C|S)` (the book's `J₁` is `Js 0` here).
(a) If `T_μ(J₁)(x) < ∞` for every `x` and `J_k ↓ J`, then `T_μ(J_k) ↓ T_μ(J)`.
(b) If `T_μ(J₁⁻)(x) < ∞` for every `x`, `g ≥ 0`, and `J_k ↑ J`, then `T_μ(J_k) ↑ T_μ(J)`.
(c) If `{J_k}` is uniformly bounded, `g` is bounded, and `J_k → J`, then `T_μ(J_k) → T_μ(J)`. -/
theorem lemma8_4_Tmu_limits {S C W : Type*}
    [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S] [BertsekasShreve.AnalyticSelection.IsBorelSpace S] [Nonempty S]
    [TopologicalSpace C] [MeasurableSpace C] [BorelSpace C] [BertsekasShreve.AnalyticSelection.IsBorelSpace C] [Nonempty C]
    [TopologicalSpace W] [MeasurableSpace W] [BorelSpace W] [BertsekasShreve.AnalyticSelection.IsBorelSpace W] [Nonempty W]
    (M : Model S C W)
    (μ : UCS M) (Js : ℕ → S → EReal) (Jl : S → EReal) (hJs : ∀ k, UMeasurable (Js k)) :
    ((∀ x, Tmu M μ (Js 0) x < ⊤) → (∀ x, Antitone fun k => Js k x) →
        (∀ x, Tendsto (fun k => Js k x) atTop (𝓝 (Jl x))) →
        (∀ x, Antitone fun k => Tmu M μ (Js k) x) ∧
          ∀ x, Tendsto (fun k => Tmu M μ (Js k) x) atTop (𝓝 (Tmu M μ Jl x))) ∧
    ((∀ x, Tmu M μ (fun y => ((negPart (Js 0) y : ENNReal) : EReal)) x < ⊤) →
        (∀ z ∈ M.Γ, 0 ≤ M.g z) → (∀ x, Monotone fun k => Js k x) →
        (∀ x, Tendsto (fun k => Js k x) atTop (𝓝 (Jl x))) →
        (∀ x, Monotone fun k => Tmu M μ (Js k) x) ∧
          ∀ x, Tendsto (fun k => Tmu M μ (Js k) x) atTop (𝓝 (Tmu M μ Jl x))) ∧
    ((∃ b : ℝ, ∀ k x, Js k x ≤ b ∧ -(b : EReal) ≤ Js k x) →
        (∃ b : ℝ, ∀ z ∈ M.Γ, M.g z ≤ b ∧ -(b : EReal) ≤ M.g z) →
        (∀ x, Tendsto (fun k => Js k x) atTop (𝓝 (Jl x))) →
        ∀ x, Tendsto (fun k => Tmu M μ (Js k) x) atTop (𝓝 (Tmu M μ Jl x))) := by sorry

end BertsekasShreve.BorelFinite

