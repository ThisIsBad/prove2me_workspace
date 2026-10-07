import Mathlib
import Definitions.Def_BalkemaDeHaan_LimitTypes_ResidualLife

namespace BalkemaDeHaan.LimitTypes

/-- `Γ_α(x) = 1 - (1 + x)^{-α}` for `x ≥ 0`, and `0` for `x < 0` (p. 793, PDF 2). -/
noncomputable def GammaLaw (α : ℝ) (x : ℝ) : ℝ :=
  if x < 0 then 0 else 1 - (1 + x) ^ (-α)

/-- `Π(x) = 1 - e^{-x}` for `x ≥ 0`, and `0` for `x < 0` (p. 793, PDF 2). -/
noncomputable def PiLaw (x : ℝ) : ℝ :=
  if x < 0 then 0 else 1 - Real.exp (-x)

/-- `Γ_{γ,α}(x) = 1 - exp(-γ [1 + α log(1 + x)])` for `x ≥ 0`, and `0` for `x < 0`, where `[·]` is
the integer part (p. 793, PDF 2). -/
noncomputable def GammaDiscreteLaw (γ α : ℝ) (x : ℝ) : ℝ :=
  if x < 0 then 0 else 1 - Real.exp (-γ * ((⌊1 + α * Real.log (1 + x)⌋ : ℤ) : ℝ))

/-- `Π_γ(x) = 1 - exp(-γ [1 + x])` for `x ≥ 0`, and `0` for `x < 0`, where `[·]` is the integer part
(p. 793, PDF 2). -/
noncomputable def PiDiscreteLaw (γ : ℝ) (x : ℝ) : ℝ :=
  if x < 0 then 0 else 1 - Real.exp (-γ * ((⌊1 + x⌋ : ℤ) : ℝ))

/-- `G` is of one of the four residual-life limit types of the introduction (p. 793):
`Π`, `Π_γ` (`γ > 0`), `Γ_α` (`α > 0`) or `Γ_{γ,α}` (`γ, α > 0`). -/
def IsResidualLimitType (G : ℝ → ℝ) : Prop :=
  IsOfType G PiLaw ∨
  (∃ γ : ℝ, 0 < γ ∧ IsOfType G (PiDiscreteLaw γ)) ∨
  (∃ α : ℝ, 0 < α ∧ IsOfType G (GammaLaw α)) ∨
  (∃ γ : ℝ, 0 < γ ∧ ∃ α : ℝ, 0 < α ∧ IsOfType G (GammaDiscreteLaw γ α))

end BalkemaDeHaan.LimitTypes
