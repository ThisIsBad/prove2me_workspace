import Mathlib
import Definitions.Def_GoldbergTarjan_Generic_Labeling

namespace GoldbergTarjan.Generic

variable {V : Type} [Fintype V] [DecidableEq V]

/-- A state of the generic algorithm: the current preflow `f` and the current labeling `d`.
The excess is not stored; it is computed from `f` by `excess`. -/
abbrev State (V : Type) : Type := (V → V → ℝ) × (V → ℕ∞)

/-- Applicability of `Push(v, w)` (Fig. 1, p. 925): `v` is active, `r_f(v, w) > 0` and
`d(v) = d(w) + 1`. -/
def PushApplicable (N : Network V) (f : V → V → ℝ) (d : V → ℕ∞) (v w : V) : Prop :=
  IsActive N f d v ∧ 0 < residualCap N f v w ∧ d v = d w + 1

/-- The amount `δ = min(e(v), r_f(v, w))` sent by `Push(v, w)` (Fig. 1). -/
noncomputable def pushAmount (N : Network V) (f : V → V → ℝ) (v w : V) : ℝ :=
  min (excess f v) (residualCap N f v w)

/-- The preflow after `Push(v, w)` (Fig. 1): `f(v, w) ← f(v, w) + δ`, `f(w, v) ← f(w, v) - δ`,
all other values unchanged. (The excess updates `e(v) ← e(v) - δ`, `e(w) ← e(w) + δ` of
Fig. 1 are consequences, since the excess is computed from `f`.) -/
noncomputable def pushFlow (N : Network V) (f : V → V → ℝ) (v w : V) : V → V → ℝ :=
  fun x y =>
    if x = v ∧ y = w then f x y + pushAmount N f v w
    else if x = w ∧ y = v then f x y - pushAmount N f v w
    else f x y

/-- `PushStep N p q v w`: the operation `Push(v, w)` is applicable in state `p` and
state `q` is the result of applying it (the labeling is unchanged). -/
def PushStep (N : Network V) (p q : State V) (v w : V) : Prop :=
  PushApplicable N p.1 p.2 v w ∧ q.1 = pushFlow N p.1 v w ∧ q.2 = p.2

/-- Applicability of `Relabel(v)` (Fig. 1, p. 925): `v` is active and
`∀ w ∈ V, r_f(v, w) > 0 ⇒ d(v) ≤ d(w)`. -/
def RelabelApplicable (N : Network V) (f : V → V → ℝ) (d : V → ℕ∞) (v : V) : Prop :=
  IsActive N f d v ∧ ∀ w, 0 < residualCap N f v w → d v ≤ d w

/-- The new label `min{d(w) + 1 | (v, w) ∈ E_f}` set by `Relabel(v)` (Fig. 1); the infimum
over the empty set is `⊤ = ∞`, matching "If this minimum is over an empty set, d(v) ← ∞". -/
noncomputable def relabelValue (N : Network V) (f : V → V → ℝ) (d : V → ℕ∞) (v : V) : ℕ∞ :=
  ⨅ (w : V) (_ : 0 < residualCap N f v w), d w + 1

/-- `RelabelStep N p q v`: the operation `Relabel(v)` is applicable in state `p` and state `q`
is the result of applying it: the preflow is unchanged and `d(v)` is set to
`min{d(w) + 1 | (v, w) ∈ E_f}`. -/
def RelabelStep (N : Network V) (p q : State V) (v : V) : Prop :=
  RelabelApplicable N p.1 p.2 v ∧ q.1 = p.1 ∧
    q.2 = Function.update p.2 v (relabelValue N p.1 p.2 v)

/-- One basic operation (a push or a relabel) leads from state `p` to state `q`. -/
def BasicStep (N : Network V) (p q : State V) : Prop :=
  (∃ v w, PushStep N p q v w) ∨ ∃ v, RelabelStep N p q v

/-- No basic operation applies in state `p` (the negation of the loop guard of Fig. 2,
"while ∃ a basic operation that applies"): the algorithm has terminated. -/
def NoBasicOpApplicable (N : Network V) (p : State V) : Prop :=
  (∀ v w, ¬ PushApplicable N p.1 p.2 v w) ∧ ∀ v, ¬ RelabelApplicable N p.1 p.2 v

end GoldbergTarjan.Generic
