import Mathlib
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_SetCoverInstance
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_elementWeight

namespace BNCovPack.SetCover

open OnlinePrimalDual.OnlineSetCover

/-- State of the Section 3 scheme with `{0,1}` coefficients, run on a set-cover instance
(Buchbinder–Naor 2009, p. 5 and p. 12). The primal variables are the sets, the covering
constraints are the arriving elements.
* `w s` is the primal variable `x(s)` (the fractional weight `w(s)` of §5.1);
* `load s` is `∑_{k : s ∋ e_k} y(k)`, the sum of the dual variables of the elements that have
  arrived so far and lie in `s` (the exponent's sum `∑_k a(s,k) y(k)` of Line (ii)b);
* `dual` is the dual value `Y = ∑_k y(k)`. -/
structure FracState (T : Type*) where
  w : T → ℝ
  load : T → ℝ
  dual : ℝ

/-- Initially every primal and dual variable is zero (p. 4: "Initially, each variable `x(i)` is
initialized to zero"). -/
def FracState.init (T : Type*) : FracState T where
  w := fun _ => 0
  load := fun _ => 0
  dual := 0

/-- Line (ii)b with `a ∈ {0,1}`, `a_i(max) = 1` and `n` replaced by `ℓ` (p. 5): when the arriving
element `e` has its dual variable at value `t`, every set `s ∋ e` has primal value
`max (w s, (1/ℓ)(exp((B/(2 c(s)))·(load s + t)) − 1))`; sets not containing `e` are unchanged. -/
noncomputable def augWeight {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (B : ℝ) (ℓ : ℕ) (st : FracState T) (e : E) (t : ℝ) :
    T → ℝ :=
  fun s => if s ∈ inst.elemSets e then
      max (st.w s) ((1 / (ℓ : ℝ)) * (Real.exp (B / (2 * inst.c s) * (st.load s + t)) - 1))
    else st.w s

/-- The value the dual variable `y(e)` reaches in the round of `e` (p. 4–5: "find the minimal
`y(j)` such that the new primal constraint is satisfied"): the least `t ≥ 0` with
`∑_{s ∋ e} w_s(t) ≥ 1`. (When no set contains `e` the set is empty and `sInf` returns `0`; the
theorems exclude this case by hypothesis.) -/
noncomputable def dualStep {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (B : ℝ) (ℓ : ℕ) (st : FracState T) (e : E) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ 1 ≤ elementWeight inst (augWeight inst B ℓ st e t) e}

open Classical in
/-- One round of the scheme (p. 5, lines (i)–(ii)) on arrival of element `e`: if the constraint
`∑_{s ∋ e} x(s) ≥ 1` already holds nothing changes (`y(e) = 0`); otherwise `y(e)` is raised to
`dualStep`, the primal variables follow `augWeight`, and the loads and the dual value are
updated. -/
noncomputable def fracStep {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (B : ℝ) (ℓ : ℕ) (st : FracState T) (e : E) : FracState T :=
  if 1 ≤ elementWeight inst st.w e then st
  else
    let y := dualStep inst B ℓ st e
    { w := augWeight inst B ℓ st e y
      load := fun s => if s ∈ inst.elemSets e then st.load s + y else st.load s
      dual := st.dual + y }

/-- The state of the scheme after the elements of the arrival list `σ` have been given, in order,
starting from the all-zero state. Elements may repeat. -/
noncomputable def fracRun {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (B : ℝ) (ℓ : ℕ) (σ : List E) : FracState T :=
  σ.foldl (fracStep inst B ℓ) (FracState.init T)

end BNCovPack.SetCover
