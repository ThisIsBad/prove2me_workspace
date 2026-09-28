import Mathlib
import Definitions.Def_GoldbergTarjan_FIFO_Network

namespace GoldbergTarjan.FIFO

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Applicability of `push(v, w)` (Fig. 1, p. 925): `v` is active, `r_f(v, w) > 0` and
`d(v) = d(w) + 1`. -/
def PushApplicable (N : Network V) (f : V → V → ℝ) (d : V → ℕ∞) (v w : V) : Prop :=
  IsActive N f d v ∧ 0 < residual N f v w ∧ d v = d w + 1

/-- The amount `δ = min(e(v), r_f(v, w))` sent by `push(v, w)` (Fig. 1). -/
def pushAmount (N : Network V) (f : V → V → ℝ) (v w : V) : ℝ :=
  min (excess f v) (residual N f v w)

/-- The preflow after the action of `push(v, w)` (Fig. 1): `f(v, w) ← f(v, w) + δ`,
`f(w, v) ← f(w, v) − δ`, every other pair unchanged, with `δ = min(e(v), r_f(v, w))`. The
excesses `e(v) ← e(v) − δ`, `e(w) ← e(w) + δ` are not stored: `excess` is recomputed from the new
function. (The action is only used when the push is applicable, where `v ≠ w`.) -/
def pushFlow (N : Network V) (f : V → V → ℝ) (v w : V) : V → V → ℝ :=
  fun x y =>
    if x = v ∧ y = w then f v w + pushAmount N f v w
    else if x = w ∧ y = v then f w v - pushAmount N f v w
    else f x y

/-- Applicability of `relabel(v)` (Fig. 1): `v` is active and for every `w ∈ V`,
`r_f(v, w) > 0 ⇒ d(v) ≤ d(w)`. -/
def RelabelApplicable (N : Network V) (f : V → V → ℝ) (d : V → ℕ∞) (v : V) : Prop :=
  IsActive N f d v ∧ ∀ w, 0 < residual N f v w → d v ≤ d w

/-- The new label set by `relabel(v)` (Fig. 1): `min{d(w) + 1 | (v, w) ∈ E_f}`, the minimum over
the residual edges leaving `v`. In `ℕ∞` the infimum of the empty family is `⊤ = ∞`, which is the
paper's "(If this minimum is over an empty set, `d(v) ← ∞`.)" -/
noncomputable def relabelLabel (N : Network V) (f : V → V → ℝ) (d : V → ℕ∞) (v : V) : ℕ∞ :=
  ⨅ (w : V) (_ : 0 < residual N f v w), d w + 1

/-- The initial preflow of Fig. 2 (p. 925): `f(v, w) = 0` for `(v, w) ∈ (V − {s}) × (V − {s})`,
and `f(s, v) = c(s, v)`, `f(v, s) = −c(s, v)` for every `v` (so `f(s, s) = 0`, as `c(s, s) = 0`). -/
def initFlow (N : Network V) : V → V → ℝ :=
  fun v w =>
    if v = N.s then N.c N.s w
    else if w = N.s then -N.c N.s v
    else 0

/-- The simple initial labeling (Fig. 2 and p. 926): `d(s) = n = |V|` and `d(v) = 0` for
`v ∈ V − {s}`. -/
def initLabel (N : Network V) : V → ℕ∞ :=
  fun v => if v = N.s then (Fintype.card V : ℕ∞) else 0

end GoldbergTarjan.FIFO
