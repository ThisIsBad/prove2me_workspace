import Mathlib
import Definitions.Def_GoldbergTarjan_FIFO_Network
import Definitions.Def_GoldbergTarjan_FIFO_PushRelabel
import Definitions.Def_GoldbergTarjan_FIFO_Algorithm

open Classical

namespace GoldbergTarjan.FIFO

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The `push/relabel(v)` operation from `σ` performs a push `push(v, w)` through its current edge
`{v, w}` (Fig. 3) and the push is nonsaturating (p. 925): `r_f(v, w) > 0` after the push. -/
def IsNonsatPush (N : Network V) (L : V → List V) (v : V) (σ : Config V) : Prop :=
  ∃ w, (L v)[σ.cur v]? = some w ∧ PushApplicable N σ.f σ.d v w ∧
    0 < residual N (pushFlow N σ.f v w) v w

/-- The `push/relabel(v)` operation from `σ` takes the relabeling branch of Fig. 3: no push is
applicable through the current edge `{v, w}` and `{v, w}` is the last edge on the edge list of `v`,
so `relabel(v)` is performed. -/
def IsRelabelOp (N : Network V) (L : V → List V) (v : V) (σ : Config V) : Prop :=
  ∃ w, (L v)[σ.cur v]? = some w ∧ ¬ PushApplicable N σ.f σ.d v w ∧ σ.cur v + 1 = (L v).length

/-- The number of nonsaturating pushes performed during the first `K` discharge operations of the
run `(S, J)`: the `k`-th discharge applies `push/relabel(v_k)` to the configurations
`prIter … (S k).cfg j`, `j < J k`, where `v_k` is the front vertex of `S k`. -/
noncomputable def nonsatPushCount (N : Network V) (L : V → List V) (K : ℕ) (S : ℕ → State V)
    (J : ℕ → ℕ) : ℕ :=
  ∑ k ∈ Finset.range K,
    ((Finset.range (J k)).filter
      (fun j => IsNonsatPush N L (frontVertex N (S k))
        (prIter N L (frontVertex N (S k)) (S k).cfg j))).card

/-- The number of relabeling operations applied to the vertex `x` during the first `K` discharge
operations of the run `(S, J)` (only discharges of `x` can relabel `x`). -/
noncomputable def relabelCountAt (N : Network V) (L : V → List V) (K : ℕ) (S : ℕ → State V)
    (J : ℕ → ℕ) (x : V) : ℕ :=
  ∑ k ∈ Finset.range K,
    if frontVertex N (S k) = x then
      ((Finset.range (J k)).filter
        (fun j => IsRelabelOp N L x (prIter N L x (S k).cfg j))).card
    else 0

/-- The total number of relabeling operations during the first `K` discharge operations. -/
noncomputable def relabelCount (N : Network V) (L : V → List V) (K : ℕ) (S : ℕ → State V)
    (J : ℕ → ℕ) : ℕ :=
  ∑ x, relabelCountAt N L K S J x

/-- The number of passes over the queue (p. 930) made by the first `K` discharge operations: the
largest pass number of a discharged queue entry (`0` if `K = 0`). -/
def passCount (K : ℕ) (S : ℕ → State V) : ℕ :=
  (Finset.range K).sup (fun k => frontPass (S k))

end GoldbergTarjan.FIFO
