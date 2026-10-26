import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_MNLBandit_UCB_Setting

namespace MNLBandit.UCB

open ChoiceCDLP.MNL

/-- The record of one completed epoch `τ` of Algorithm 1: its assortment `S_τ` and the purchase
counts `v̂_{i,τ}` (3.1) of every product in that epoch. -/
abbrev EpochRecord (N : ℕ) := Finset (Fin N) × (Fin N → ℕ)

/-- `T_i(ℓ) = |{τ ≤ ℓ : i ∈ S_τ}|` (3.2), for the list `past` of the `ℓ = past.length` completed
epochs. -/
def TcountL {N : ℕ} (past : List (EpochRecord N)) (i : Fin N) : ℕ :=
  (past.filter (fun e => decide (i ∈ e.1))).length

/-- `v̄_{i,ℓ} = (1 / T_i(ℓ)) ∑_{τ ∈ 𝒯_i(ℓ)} v̂_{i,τ}` (3.3) for the list `past` of completed epochs.
Only used when `T_i(ℓ) ≥ 1`. -/
noncomputable def vbarL {N : ℕ} (past : List (EpochRecord N)) (i : Fin N) : ℝ :=
  ((past.filter (fun e => decide (i ∈ e.1))).map (fun e => (e.2 i : ℝ))).sum / (TcountL past i : ℝ)

/-- The upper confidence bound (3.4) after the `ℓ = past.length` completed epochs `past`:
`v^UCB_{i,ℓ} = v̄_{i,ℓ} + √(v̄_{i,ℓ} · 48 log(√N ℓ + 1) / T_i(ℓ)) + 48 log(√N ℓ + 1) / T_i(ℓ)`.
While product `i` has never been offered (`T_i(ℓ) = 0`) the value is `1`, the initialization
`v^UCB_{i,0} = 1` of Algorithm 1, line 1. -/
noncomputable def vUCBL {N : ℕ} (past : List (EpochRecord N)) (i : Fin N) : ℝ :=
  if TcountL past i = 0 then 1 else
    vbarL past i
      + Real.sqrt (vbarL past i * (48 * Real.log (Real.sqrt N * (past.length : ℝ) + 1))
          / (TcountL past i : ℝ))
      + 48 * Real.log (Real.sqrt N * (past.length : ℝ) + 1) / (TcountL past i : ℝ)

/-- The optimistic assortment (3.6)–(3.7): the selector's maximizer over `𝒮` of
`R̃(S) = ∑_{i ∈ S} r_i v^UCB_i / (1 + ∑_{j ∈ S} v^UCB_j)` computed from the completed epochs
`past`. -/
noncomputable def optimisticSet {N : ℕ} (r : Fin N → ℝ)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (past : List (EpochRecord N)) :
    Finset (Fin N) :=
  sel (fun S => mnlObjective (fun i => vUCBL past i) r 1 S)

/-- The internal state of Algorithm 1: the completed epochs, the assortment of the current epoch,
and the purchase counts of the current epoch so far. -/
structure AlgState (N : ℕ) where
  past : List (EpochRecord N)
  cur : Finset (Fin N)
  counts : Fin N → ℕ

/-- Initial state (lines 1–2): no completed epoch, the first assortment is the argmax of `R̃`
with `v^UCB_{i,0} = 1`, no purchases yet. -/
noncomputable def initState {N : ℕ} (r : Fin N → ℝ)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) : AlgState N :=
  ⟨[], optimisticSet r sel [], fun _ => 0⟩

/-- One customer's outcome updates the state (lines 5–14). A no-purchase closes the current epoch:
its assortment and counts are appended to the completed epochs, the UCBs are recomputed, and the next
epoch's assortment is the new optimistic assortment. A purchase of `i` increments `i`'s count. -/
noncomputable def step {N : ℕ} (r : Fin N → ℝ)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (s : AlgState N) :
    Option (Fin N) → AlgState N
  | none =>
      ⟨s.past ++ [(s.cur, s.counts)], optimisticSet r sel (s.past ++ [(s.cur, s.counts)]),
        fun _ => 0⟩
  | some i => ⟨s.past, s.cur, Function.update s.counts i (s.counts i + 1)⟩

/-- The state of Algorithm 1 after the outcomes `cs`, in order. -/
noncomputable def runAlg {N : ℕ} (r : Fin N → ℝ)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (cs : List (Option (Fin N))) : AlgState N :=
  cs.foldl (step r sel) (initState r sel)

/-- Algorithm 1 (p. 9) as a policy: customer `t` is offered the assortment of the current epoch
after the choices of customers `0, …, t - 1`. It uses only the revenues `r`, the selector `sel`
(which encodes `𝒮` and the tie-breaking rule) and the observed choices, never `v`. -/
noncomputable def alg1 {N : ℕ} (r : Fin N → ℝ)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) : Policy N :=
  fun _ pre => (runAlg r sel (List.ofFn pre)).cur

/-- The state of Algorithm 1 after the whole history `h`. -/
noncomputable def finalState {N T : ℕ} (r : Fin N → ℝ)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (h : History N T) : AlgState N :=
  runAlg r sel (List.ofFn h)

/-- The number of epochs completed within the history `h` (the number of no-purchases). -/
noncomputable def epochsDone {N T : ℕ} (r : Fin N → ℝ)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (h : History N T) : ℕ :=
  (finalState r sel h).past.length

/-- The first `ℓ` completed epochs of `h` (epochs `1, …, ℓ`), for `ℓ ≤ epochsDone h`. -/
noncomputable def pastUpTo {N T : ℕ} (r : Fin N → ℝ)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (h : History N T) (ℓ : ℕ) :
    List (EpochRecord N) :=
  (finalState r sel h).past.take ℓ

/-- `T_i(ℓ)` (3.2) along `h`, after `ℓ` completed epochs. -/
noncomputable def Tcount {N T : ℕ} (r : Fin N → ℝ)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (h : History N T) (i : Fin N) (ℓ : ℕ) : ℕ :=
  TcountL (pastUpTo r sel h ℓ) i

/-- `v̄_{i,ℓ}` (3.3) along `h`, after `ℓ` completed epochs. -/
noncomputable def vbar {N T : ℕ} (r : Fin N → ℝ)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (h : History N T) (i : Fin N) (ℓ : ℕ) : ℝ :=
  vbarL (pastUpTo r sel h ℓ) i

/-- `v^UCB_{i,ℓ}` (3.4) along `h`, after `ℓ` completed epochs. -/
noncomputable def vUCB {N T : ℕ} (r : Fin N → ℝ)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (h : History N T) (i : Fin N) (ℓ : ℕ) : ℝ :=
  vUCBL (pastUpTo r sel h ℓ) i

/-- `S_{ℓ+1}`, the assortment Algorithm 1 offers in epoch `ℓ + 1`, computed at the end of epoch `ℓ`
from `v^UCB_{·,ℓ}` (3.6); `nextSet r sel h 0 = S_1`. -/
noncomputable def nextSet {N T : ℕ} (r : Fin N → ℝ)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (h : History N T) (ℓ : ℕ) : Finset (Fin N) :=
  optimisticSet r sel (pastUpTo r sel h ℓ)

/-- `L`, the number of epochs started within the first `T` customers of `h`: `0` if `T = 0`, and
otherwise one plus the number of no-purchases among customers `0, …, T - 2`. -/
def epochsStarted {N T : ℕ} (h : History N T) : ℕ :=
  if T = 0 then 0 else
    (Finset.univ.filter (fun t : Fin T => t.val + 1 < T ∧ h t = none)).card + 1

end MNLBandit.UCB
