import Mathlib
import Definitions.Def_SteinitzExchange_Extension_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Extension_Exchange

namespace SteinitzExchange.Extension

/-- Murota 1996, p. 282, Lemma 3.2. With the paper's convention `ω_p(x, u, v) = −∞` when
`x − χ_u + χ_v ∉ B`, the bound `ω_p(y) − ω_p(x) ≤ max(π₀₀ + π₁₁, π₀₁ + π₁₀)` says: for one of the
two pairings, both exchanged points lie in `B` and the bound holds with that pairing. -/
theorem two_swap_bound {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ)
    (hloc : SatisfiesEXCLoc B ω) (x : V → ℤ) (hx : x ∈ B) (u₀ u₁ v₀ v₁ : V)
    (hy : x - chi u₀ - chi u₁ + chi v₀ + chi v₁ ∈ B)
    (h00 : u₀ ≠ v₀) (h01 : u₀ ≠ v₁) (h10 : u₁ ≠ v₀) (h11 : u₁ ≠ v₁) (p : V → ℝ) :
    let y := x - chi u₀ - chi u₁ + chi v₀ + chi v₁
    let π : V → V → ℝ := fun u v => perturb ω p (x - chi u + chi v) - perturb ω p x
    (x - chi u₀ + chi v₀ ∈ B ∧ x - chi u₁ + chi v₁ ∈ B ∧
        perturb ω p y - perturb ω p x ≤ π u₀ v₀ + π u₁ v₁) ∨
      (x - chi u₀ + chi v₁ ∈ B ∧ x - chi u₁ + chi v₀ ∈ B ∧
        perturb ω p y - perturb ω p x ≤ π u₀ v₁ + π u₁ v₀) := by sorry

end SteinitzExchange.Extension
