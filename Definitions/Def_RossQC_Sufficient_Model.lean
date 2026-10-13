import Mathlib
import Definitions.Def_RossQC_Regions_Model
open Filter

namespace RossQC.Sufficient

/-- Ross, *Quality Control under Markovian Deterioration*, §3, p. 590.
`P` is the probability of the bad state; the parameters satisfy the standing
assumptions in the theorem statements. -/
structure Model where
  β : ℝ
  π : ℝ
  C : ℝ
  I : ℝ
  R : ℝ

/-- Ross, §3, p. 590: `TP = P + π − πP`. -/
def Model.T (M : Model) (P : ℝ) : ℝ := P + M.π - M.π * P

/-- Ross, §3, equation (3), p. 590: the cost of each action followed by
continuation value `V`. Inspection reveals the current state; revision resets
the next belief to `π`. -/
def Model.rhs3 (M : Model) (V : ℝ → ℝ) (P : ℝ) : RossQC.Regions.Action → ℝ
  | .produce => M.C * P + M.β * V (M.T P)
  | .inspect => M.I + M.β * P * V 1 + M.β * (1 - P) * V M.π
  | .revise => M.R + M.β * V M.π

/-- Ross, §3, equation (4), p. 590. Stage zero has zero cost, and stage one
is `min {CP, I, R}`. -/
def Model.valueIter (M : Model) : ℕ → ℝ → ℝ
  | 0, _ => 0
  | n + 1, P => min (M.rhs3 (M.valueIter n) P .produce)
      (min (M.rhs3 (M.valueIter n) P .inspect)
           (M.rhs3 (M.valueIter n) P .revise))

/-- Ross, §2, p. 589 and §3, equation (4), p. 590. The discounted value is
the limit of finite-horizon values; convergence is asserted in the theorem
for equation (3). -/
noncomputable def Model.value (M : Model) (P : ℝ) : ℝ :=
  limUnder atTop (fun n => M.valueIter n P)

/-- Ross, Theorem 3.7(a), p. 592. At a threshold equality the later action
is chosen. A threshold above one gives an empty revise interval on `[0,1]`. -/
noncomputable def Model.threeRegion (_M : Model) (P₁ P₂ P : ℝ) : RossQC.Regions.Action :=
  if P < P₁ then .produce else if P < P₂ then .inspect else .revise

/-- Ross, Theorem 3.7(b), p. 592. A threshold above one produces everywhere
on the admissible belief interval. -/
noncomputable def Model.twoRegion (_M : Model) (P₁ P : ℝ) : RossQC.Regions.Action :=
  if P < P₁ then .produce else .revise

end RossQC.Sufficient
