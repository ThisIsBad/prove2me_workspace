import Mathlib
import Definitions.Def_ServiceParts_UnitDecomp_Model

open scoped ENNReal NNReal

namespace ServiceParts.UnitDecomp

variable {σ : Type} [Fintype σ]

/-- The configuration `(z, y)` of a subsystem `S_w` at the beginning of a period: `z` is the
location of unit `w` and `y` the distance of customer `w` (Definition 1, p. 26, and the
sufficient state `x^w_n = (sₙ, z_{wn}, y_{wn})` of p. 27, without its Markov component). -/
abbrev SubState := ℕ × ℕ

/-- A Markov policy for a subsystem: a decision for its unit from the period, the Markov
state and the subsystem configuration. The decision only has an effect when the unit is at
the supplier location `m + 1`. -/
abbrev SubPolicy (σ : Type) := ℕ → σ → SubState → Decision

/-- Events 2–4 of a period for a subsystem under the commitment constraint of Definition 3
(unit `w` serves customer `w`): the unit moves (released or not), the customer moves by the
demand `d`, and if afterwards the unit is on hand and the customer waiting, both are used up
(location `0`, distance `0`). -/
def Model.subPost (M : Model σ) (x : SubState) (a : Decision) (d : ℕ) : SubState :=
  let z := unitMove M.m x.1 (decide (a = Decision.release))
  let y := custMove d x.2
  if z = 1 ∧ y = 1 then (0, 0) else (z, y)

/-- Event 5 for a subsystem: `h` if its unit is on hand and `b` if its customer is waiting
at the end of the period. -/
noncomputable def Model.subStage (M : Model σ) (x : SubState) : ℝ≥0∞ :=
  (if x.1 = 1 then (M.h : ℝ≥0∞) else 0) + (if x.2 = 1 then (M.b : ℝ≥0∞) else 0)

/-- Expected discounted cost of the subsystem policy `ρ` in periods `n, n + 1, …, N` from
Markov state `s` and configuration `x` in period `n`. -/
noncomputable def Model.subCost (M : Model σ) (N : ℕ) (ρ : SubPolicy σ) (n : ℕ) (s : σ)
    (x : SubState) : ℝ≥0∞ :=
  M.costToGo M.subPost M.subStage ρ (N + 1 - n) n s x

/-- Optimal expected discounted cost of a subsystem in periods `n, …, N`: the infimum of
`subCost` over all Markov subsystem policies. -/
noncomputable def Model.subOpt (M : Model σ) (N n : ℕ) (s : σ) (x : SubState) : ℝ≥0∞ :=
  ⨅ ρ : SubPolicy σ, M.subCost N ρ n s x

/-- Expected cost of taking decision `a` in period `n` (state `s`, configuration `x`) and
acting optimally in periods `n + 1, …, N`. -/
noncomputable def Model.subQ (M : Model σ) (N n : ℕ) (s : σ) (x : SubState) (a : Decision) :
    ℝ≥0∞ :=
  ∑' d : ℕ, M.demand s d *
    (M.subStage (M.subPost x a d) +
      (M.α : ℝ≥0∞) * ∑ s' : σ, M.trans s s' * M.subOpt N (n + 1) s' (M.subPost x a d))

/-- `R*ₙ(s, y)` (p. 28): the set of optimal decisions in period `n` for a subsystem whose
Markov state is `s`, whose customer is at distance `y` and whose unit is at the supplier
location `m + 1`. -/
noncomputable def Model.optDecisions (M : Model σ) (N n : ℕ) (s : σ) (y : ℕ) : Set Decision :=
  {a | ∀ a' : Decision, M.subQ N n s (M.m + 1, y) a ≤ M.subQ N n s (M.m + 1, y) a'}

/-- The critical distance `y*(n, s) = max {y : R*ₙ(s, y) ⊇ {Release}}` (p. 29), taken as a
supremum in `ℕ∞`: it is `⊤` when releasing is optimal at arbitrarily large distances, and `0`
when the set is empty. -/
noncomputable def Model.criticalDistance (M : Model σ) (N n : ℕ) (s : σ) : ℕ∞ :=
  ⨆ (y : ℕ) (_ : Decision.release ∈ M.optDecisions N n s y), (y : ℕ∞)

/-- The critical distance policy `Rₙ(s, y) = {Release}` iff `y ≤ y*(n, s)` (p. 29). -/
noncomputable def Model.criticalPolicy (M : Model σ) (N : ℕ) : SubPolicy σ :=
  fun n s x => if (x.2 : ℕ∞) ≤ M.criticalDistance N n s then Decision.release else Decision.hold

end ServiceParts.UnitDecomp
