import Mathlib

namespace TeschlODE.Horseshoe

/-- Teschl, §13.1, p. 332, (13.1)–(13.3): `F : ℝ² → ℝ²` is a Smale horseshoe map with parameters
`λ`, `µ` if on the strips `J₀ = [0, 1] × [0, 1/µ]` and `J₁ = [0, 1] × [1 − 1/µ, 1]` it is given by
`F(x, y) = (λx, µy)` on `J₀` (13.2) and `F(x, y) = (1 − λx, µ(1 − y))` on `J₁` (13.3). The book
describes the map analytically only on `J₀ ∪ J₁` ("we only describe this part of the map
analytically", p. 331), so its values elsewhere are left arbitrary. For `µ > 2` the strips are
disjoint, so such maps exist. -/
def IsHorseshoeMap (lam μ : ℝ) (F : ℝ × ℝ → ℝ × ℝ) : Prop :=
  (∀ p ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) (1 / μ), F p = (lam * p.1, μ * p.2)) ∧
    (∀ p ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (1 - 1 / μ) 1, F p = (1 - lam * p.1, μ * (1 - p.2)))

end TeschlODE.Horseshoe
