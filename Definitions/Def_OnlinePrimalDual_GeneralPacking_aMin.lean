import Mathlib
import Definitions.Def_OnlinePrimalDual_GeneralPacking_GeneralInstance

namespace OnlinePrimalDual.GeneralPacking

/-- `aᵢ(min) = minₖ{a(i,k) ∣ a(i,k) ≠ 0}` (Buchbinder & Naor, FnT TCS 2009, Theorem 14.1, p. 249):
the smallest *non-zero* coefficient of primal variable `i` across every constraint, `0` (a junk
value, never exercised where this quantity is actually used — see `STATUS.md`) if `i` has no
non-zero coefficient at all. -/
noncomputable def aMin {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (inst : GeneralInstance I J) (i : I) : ℝ :=
  if h : ((Finset.univ.filter (fun k => inst.a i k ≠ 0)).image (inst.a i)).Nonempty then
    (((Finset.univ.filter (fun k => inst.a i k ≠ 0)).image (inst.a i))).min' h
  else 0

end OnlinePrimalDual.GeneralPacking
