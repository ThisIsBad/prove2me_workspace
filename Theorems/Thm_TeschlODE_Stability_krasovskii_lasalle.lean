import Mathlib
import Definitions.Def_TeschlODE_Stability_IsIntegralCurve
import Definitions.Def_TeschlODE_Stability_IsMaximalFlow
import Definitions.Def_TeschlODE_Stability_IsLiapunovFunction
import Definitions.Def_TeschlODE_Stability_IsStrictLiapunovFunction
import Definitions.Def_TeschlODE_Stability_semiOrbit
import Definitions.Def_TeschlODE_Stability_orbit
import Definitions.Def_TeschlODE_Stability_IsStable
import Definitions.Def_TeschlODE_Stability_IsAsymptoticallyStable

namespace TeschlODE.Stability

theorem krasovskii_lasalle {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (M : Set (EuclideanSpace ℝ (Fin n))) (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M)
    (I : EuclideanSpace ℝ (Fin n) → Set ℝ)
    (Φ : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hΦ : IsMaximalFlow f M I Φ)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ M) (hfix : f x₀ = 0)
    (U : Set (EuclideanSpace ℝ (Fin n))) (L : EuclideanSpace ℝ (Fin n) → ℝ)
    (hL : IsLiapunovFunction f M x₀ U L) :
    -- (i) L not constant on any orbit lying entirely in U \ {x₀} ⇒ x₀ asymptotically stable
    ((∀ y ∈ M, orbit I Φ y ⊆ U \ {x₀} → ∃ a ∈ orbit I Φ y, ∃ b ∈ orbit I Φ y, L a ≠ L b) →
      IsAsymptoticallyStable M I Φ x₀) ∧
    -- (ii) a strict Liapunov function is not constant on any orbit lying entirely in U \ {x₀}
    (IsStrictLiapunovFunction f M x₀ U L →
      ∀ y ∈ M, orbit I Φ y ⊆ U \ {x₀} → ∃ a ∈ orbit I Φ y, ∃ b ∈ orbit I Φ y, L a ≠ L b) ∧
    -- (iii) under the hypothesis of (i), every forward orbit lying in a compact subset of U
    -- exists for all t ≥ 0 and converges to x₀
    ((∀ y ∈ M, orbit I Φ y ⊆ U \ {x₀} → ∃ a ∈ orbit I Φ y, ∃ b ∈ orbit I Φ y, L a ≠ L b) →
      ∀ x ∈ M, ∀ C : Set (EuclideanSpace ℝ (Fin n)), IsCompact C → C ⊆ U →
        semiOrbit 1 I Φ x ⊆ C →
        (∀ t : ℝ, 0 ≤ t → t ∈ I x) ∧
          Filter.Tendsto (fun t => Φ t x) Filter.atTop (nhds x₀)) := by sorry

end TeschlODE.Stability

