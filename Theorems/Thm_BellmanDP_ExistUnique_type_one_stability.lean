import Mathlib
import Definitions.Def_BellmanDP_ExistUnique_SupEquation
import Definitions.Def_BellmanDP_ExistUnique_EquationTypes

namespace BellmanDP.ExistUnique

/-- Bellman, *Dynamic Programming*, Ch. IV, § 6, Theorem 3, p. 124. Let
`f(p) = Sup_q [g + h f(T)]` and `F(p) = Sup_q [G + h F(T)]` both be of Type One (same `h`, `T`,
`a`), and let `f`, `F` be their solutions vanishing at `θ` and continuous there. With
`u(c) = Sup_{‖p‖ ≤ c} Sup_q |G(p, q) − g(p, q)|`,
`Sup_{‖p‖ ≤ c} |F(p) − f(p)| ≤ Σ_{n=0}^∞ u(aⁿ c)`. -/
theorem type_one_stability {N : ℕ} {S : Type*} [Nonempty S]
    (D : Set (EuclideanSpace ℝ (Fin N))) (g G h : EuclideanSpace ℝ (Fin N) → S → ℝ)
    (T : EuclideanSpace ℝ (Fin N) → S → EuclideanSpace ℝ (Fin N)) (a : ℝ)
    (hg : TypeOne D g h T a) (hG : TypeOne D G h T a)
    (f F : EuclideanSpace ℝ (Fin N) → ℝ)
    (hf_cont : ContinuousWithinAt f D 0) (hf_zero : f 0 = 0)
    (hf : ∀ p ∈ D, p ≠ 0 → SolvesAt g h T f p)
    (hF_cont : ContinuousWithinAt F D 0) (hF_zero : F 0 = 0)
    (hF : ∀ p ∈ D, p ≠ 0 → SolvesAt G h T F p) (c : ℝ) :
    ∀ p ∈ D, ‖p‖ ≤ c →
      |F p - f p| ≤ ∑' n : ℕ, radialSup D (fun p q => G p q - g p q) (a ^ n * c) := by sorry

end BellmanDP.ExistUnique

