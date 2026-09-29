import Mathlib
import Definitions.Def_WeylPolyhedra_Shared_Representable
import Definitions.Def_WeylPolyhedra_Shared_NonDegenerate
import Definitions.Def_WeylPolyhedra_Shared_IsExtremeSupport

namespace WeylPolyhedra.Pyramid

/-- Weyl (1935), §2 a), p. 293 (the induction step of case a)), in the coordinates the paper
chooses there: `n = m + 1 ≥ 2`, and `xₙ ≥ 0` (the normal `Pi.single (Fin.last m) 1`) is an
extreme support of the finite non-degenerate system `S ⊆ ℝⁿ`. `S₀` is the set of points of `S`
with `xₙ = 0`, viewed in `ℝ^(n-1)` by dropping the last coordinate (`Fin.init`), and `S'` is the
set of the other points of `S`. Let `β` be any extreme support of `S₀` in `ℝ^(n-1)` (inequality
(5)) and let `μ` be the minimum of `(β₁x₁ + ⋯ + β_{n-1}x_{n-1}) / xₙ` over the points `x` of
`S'`, attained at some `a ∈ S'`. Then the inequality (6)
`β₁x₁ + ⋯ + β_{n-1}x_{n-1} - μ xₙ ≥ 0`, i.e. the normal `(β₁, …, β_{n-1}, -μ)`, is an extreme
support of `S`. -/
theorem lift_extreme_support {m : ℕ} (hm : 1 ≤ m) (S : Finset (Fin (m + 1) → ℝ))
    (hS : Shared.NonDegenerate S)
    (hlast : Shared.IsExtremeSupport S (Pi.single (Fin.last m) 1))
    (β : Fin m → ℝ)
    (hβ : Shared.IsExtremeSupport ((S.filter (fun x => x (Fin.last m) = 0)).image Fin.init) β)
    (μ : ℝ)
    (hμ_attained : ∃ a ∈ S.filter (fun x => x (Fin.last m) ≠ 0),
      μ = (β ⬝ᵥ Fin.init a) / a (Fin.last m))
    (hμ_min : ∀ x ∈ S.filter (fun x => x (Fin.last m) ≠ 0),
      μ ≤ (β ⬝ᵥ Fin.init x) / x (Fin.last m)) :
    Shared.IsExtremeSupport S (Fin.snoc β (-μ) : Fin (m + 1) → ℝ) := by sorry

end WeylPolyhedra.Pyramid

