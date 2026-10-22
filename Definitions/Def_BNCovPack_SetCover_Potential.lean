import Mathlib
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_SetCoverInstance
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_elementWeight
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_coveredBy

namespace BNCovPack.SetCover

open OnlinePrimalDual.OnlineSetCover

/-- The constant `r = e · ln(e/(e − 1))` of §5.1 (p. 13). -/
noncomputable def rConst : ℝ := Real.exp 1 * Real.log (Real.exp 1 / (Real.exp 1 - 1))

/-- The parameter `α = max {1, ln(r n / OPT)}` (p. 13), where `n` is the number of elements of
the ground set and `OPT` the (known) optimum value. -/
noncomputable def alphaParam (n OPT : ℕ) : ℝ :=
  max 1 (Real.log (rConst * (n : ℝ) / (OPT : ℝ)))

/-- `f(e) = min {1, exp(−α + α ∑_{s ∋ e} w(s))}` (p. 12). -/
noncomputable def fval {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (α : ℝ) (w : T → ℝ) (e : E) : ℝ :=
  min 1 (Real.exp (-α + α * elementWeight inst w e))

open Classical in
/-- `Φ₁ = 1 − ∏_{e ∉ C̄} (1 − f(e))` (p. 12): the product ranges over all elements of the ground
set that are not covered by the current family `C`, whether or not they have arrived. -/
noncomputable def potential1 {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (α : ℝ) (w : T → ℝ) (C : Finset T) : ℝ :=
  1 - ∏ e ∈ Finset.univ.filter (fun e => ¬ coveredBy inst C e), (1 - fval inst α w e)

/-- `Φ₂ = exp(∑_{s ∈ 𝒮} ((ln 2)·χ_C(s) − α w(s)) − OPT)` (p. 12), with `χ_C(s) = 1` if `s ∈ C`
and `0` otherwise. -/
noncomputable def potential2 {T : Type*} [Fintype T] [DecidableEq T]
    (α : ℝ) (OPT : ℕ) (w : T → ℝ) (C : Finset T) : ℝ :=
  Real.exp (∑ s, (Real.log 2 * (if s ∈ C then (1 : ℝ) else 0) - α * w s) - (OPT : ℝ))

/-- The potential function `Φ = Φ₁ + Φ₂` of §5.1 (p. 12). -/
noncomputable def potential {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (α : ℝ) (OPT : ℕ) (w : T → ℝ) (C : Finset T) : ℝ :=
  potential1 inst α w C + potential2 α OPT w C

end BNCovPack.SetCover
