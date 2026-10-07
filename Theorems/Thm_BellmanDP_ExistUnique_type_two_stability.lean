import Mathlib
import Definitions.Def_BellmanDP_ExistUnique_SupEquation
import Definitions.Def_BellmanDP_ExistUnique_EquationTypes

namespace BellmanDP.ExistUnique

/-- Bellman, *Dynamic Programming*, Ch. IV, § 6, Theorem 4, p. 124 (corrected). Let
`f(p) = Sup_q [g + h f(T)]` and `F(p) = Sup_q [G + h F(T)]` both be of Type Two (same `h`, `T`),
with solutions `f`, `F` bounded in every finite part of `D`. Let `c` be such that `|h| ≤ a < 1`
on `{p ∈ D : ‖p‖ ≤ c}` and `T` maps that set into `‖·‖ ≤ c` (automatic for every `c` under the
first alternative `‖T(p, q)‖ ≤ ‖p‖` of Type Two). Then
`Sup_{‖p‖ ≤ c} |F(p) − f(p)| ≤ u(c)/(1 − a)`, `u(c) = Sup_{‖p‖ ≤ c} Sup_q |G(p, q) − g(p, q)|`.
The ball-invariance hypothesis is added to the printed statement, which fails without it
under the bounded-domain alternative. -/
theorem type_two_stability {N : ℕ} {S : Type*} [Nonempty S]
    (D : Set (EuclideanSpace ℝ (Fin N))) (g G h : EuclideanSpace ℝ (Fin N) → S → ℝ)
    (T : EuclideanSpace ℝ (Fin N) → S → EuclideanSpace ℝ (Fin N))
    (hg : TypeTwo D g h T) (hG : TypeTwo D G h T)
    (f F : EuclideanSpace ℝ (Fin N) → ℝ)
    (hf_bdd : BoundedOnBoundedParts D f) (hf : ∀ p ∈ D, SolvesAt g h T f p)
    (hF_bdd : BoundedOnBoundedParts D F) (hF : ∀ p ∈ D, SolvesAt G h T F p)
    (c a : ℝ) (ha : a < 1) (hh : ∀ p ∈ D, ‖p‖ ≤ c → ∀ q : S, |h p q| ≤ a)
    (hTc : ∀ p ∈ D, ‖p‖ ≤ c → ∀ q : S, ‖T p q‖ ≤ c) :
    ∀ p ∈ D, ‖p‖ ≤ c →
      |F p - f p| ≤ radialSup D (fun p q => G p q - g p q) c / (1 - a) := by sorry

end BellmanDP.ExistUnique

