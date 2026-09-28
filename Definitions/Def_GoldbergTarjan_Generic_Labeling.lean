import Mathlib
import Definitions.Def_GoldbergTarjan_Generic_Preflow

namespace GoldbergTarjan.Generic

variable {V : Type} [Fintype V]

/-- A valid labeling (p. 924): a function `d` from the vertices to the nonnegative integers
and infinity (`ℕ∞`) such that `d(s) = n`, `d(t) = 0`, and `d(v) ≤ d(w) + 1` for every
residual edge `(v, w)`, where `n = |V|`. -/
def IsValidLabeling (N : Network V) (f : V → V → ℝ) (d : V → ℕ∞) : Prop :=
  d N.s = (Fintype.card V : ℕ∞) ∧ d N.t = 0 ∧
    ∀ v w, IsResidualEdge N f v w → d v ≤ d w + 1

/-- A vertex `v` is active (p. 925) if `v ∈ V - {s, t}`, `d(v) < ∞` and `e(v) > 0`. -/
def IsActive (N : Network V) (f : V → V → ℝ) (d : V → ℕ∞) (v : V) : Prop :=
  v ≠ N.s ∧ v ≠ N.t ∧ d v < ⊤ ∧ 0 < excess f v

end GoldbergTarjan.Generic
