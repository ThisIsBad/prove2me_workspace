import Mathlib
import Definitions.Def_GoldbergTarjan_Generic_Operations

namespace GoldbergTarjan.Generic

open Classical

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The initial preflow of Fig. 2 (p. 925): `f(s, v) = c(s, v)`, `f(v, s) = -c(s, v)` for every
`v`, and `f(v, w) = 0` for `v, w ≠ s`. (With `c(s, s) = 0` both assignments give `f(s, s) = 0`.) -/
def initialFlow (N : Network V) : V → V → ℝ :=
  fun v w => if v = N.s then N.c N.s w else if w = N.s then -N.c N.s v else 0

/-- The simple initial labeling (p. 926): `d(s) = n` and `d(v) = 0` for `v ∈ V - {s}`. -/
noncomputable def initialLabel (N : Network V) : V → ℕ∞ :=
  fun v => if v = N.s then (Fintype.card V : ℕ∞) else 0

/-- The initial state of the generic algorithm (Fig. 2 with the simple labeling). -/
noncomputable def initialState (N : Network V) : State V :=
  (initialFlow N, initialLabel N)

/-- `IsRun N σ K`: `σ 0, σ 1, …, σ K` is an execution of the generic algorithm (Fig. 2) with
`K` basic operations: it starts from the initial state, and each `σ (k + 1)` (`k < K`) is
obtained from `σ k` by one applicable push or relabel, chosen in any order. The values of
`σ` beyond `K` are irrelevant. -/
def IsRun (N : Network V) (σ : ℕ → State V) (K : ℕ) : Prop :=
  σ 0 = initialState N ∧ ∀ k < K, BasicStep N (σ k) (σ (k + 1))

/-- The number of relabeling operations applied to the vertex `v` among the first `K` steps
of `σ`. -/
noncomputable def relabelCountAt (N : Network V) (σ : ℕ → State V) (K : ℕ) (v : V) : ℕ :=
  ((Finset.range K).filter (fun k => RelabelStep N (σ k) (σ (k + 1)) v)).card

/-- The number of relabeling operations among the first `K` steps of `σ`. -/
noncomputable def relabelCount (N : Network V) (σ : ℕ → State V) (K : ℕ) : ℕ :=
  ((Finset.range K).filter (fun k => ∃ v, RelabelStep N (σ k) (σ (k + 1)) v)).card

/-- The number of saturating pushes among the first `K` steps of `σ`: steps that are a
`Push(v, w)` after which `r_f(v, w) = 0` (p. 925). -/
noncomputable def saturatingPushCount (N : Network V) (σ : ℕ → State V) (K : ℕ) : ℕ :=
  ((Finset.range K).filter (fun k => ∃ v w, PushStep N (σ k) (σ (k + 1)) v w ∧
    residualCap N (σ (k + 1)).1 v w = 0)).card

/-- The number of nonsaturating pushes among the first `K` steps of `σ`: steps that are a
`Push(v, w)` after which `r_f(v, w) > 0` (p. 925). -/
noncomputable def nonsaturatingPushCount (N : Network V) (σ : ℕ → State V) (K : ℕ) : ℕ :=
  ((Finset.range K).filter (fun k => ∃ v w, PushStep N (σ k) (σ (k + 1)) v w ∧
    0 < residualCap N (σ (k + 1)).1 v w)).card

end GoldbergTarjan.Generic
