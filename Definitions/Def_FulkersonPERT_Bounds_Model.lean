import Mathlib
import Definitions.Def_CriticalPath_Events_ProjectNetwork
import Definitions.Def_CriticalPath_Events_EventTimes

namespace FulkersonPERT.Bounds

open CriticalPath.Events
open scoped Classical

variable {n : ℕ}

/-- Bundle distributions, Fulkerson (1962) §3, (3.1)–(3.3), pp. 4–5. For every event `j` the
bundle `B_j` consists of the arcs `(i, j)` with `i ∈ N.pred j`; a *bundle vector* at `j` is a
function `v : Fin (n + 1) → ℝ` where `v i` is the length of arc `(i, j)` (coordinates outside
`N.pred j` are carried but never read). `supp j` is the finite support of the bundle's
distribution and `p j v` the probability of the bundle vector `v`. -/
structure BundleDist (n : ℕ) where
  /-- The finite support of the distribution of the bundle vector at event `j`. -/
  supp : Fin (n + 1) → Finset (Fin (n + 1) → ℝ)
  /-- `p j v` is the probability `p(t_{B_j})` of the bundle vector `v` at event `j`, (3.3). -/
  p : Fin (n + 1) → (Fin (n + 1) → ℝ) → ℝ

/-- Each bundle distribution is a probability distribution on its finite support. -/
def BundleDist.IsProb (D : BundleDist n) : Prop :=
  (∀ j, ∀ v ∈ D.supp j, 0 ≤ D.p j v) ∧ ∀ j, ∑ v ∈ D.supp j, D.p j v = 1

/-- The arc lengths of an assignment `ω` of bundle vectors, (3.4): `ω j` is the bundle vector of
event `j`, so the length of arc `(i, j)` is `ω j i`. -/
def arcLengths (ω : Fin (n + 1) → Fin (n + 1) → ℝ) : Fin (n + 1) → Fin (n + 1) → ℝ :=
  fun i j => ω j i

/-- The probability of an assignment under independence between bundles, (3.5):
`p(t) = p(t_{B_1}) ⋯ p(t_{B_n})`. -/
noncomputable def prob (D : BundleDist n) (ω : Fin (n + 1) → Fin (n + 1) → ℝ) : ℝ :=
  ∏ j, D.p j (ω j)

/-- The expected critical path length `e_i = Σ_t p(t) ℓ_i(t)`, (3.7): the sum over every
assignment of bundle vectors from the supports, weighted by the product probability (3.5), of the
critical path length `ℓ_i(t)` (Kelley's earliest event time). -/
noncomputable def expectedLength (N : ProjectNetwork n) (D : BundleDist n) (i : Fin (n + 1)) :
    ℝ :=
  ∑ ω ∈ Fintype.piFinset D.supp, prob D ω * earliest N (arcLengths ω) i

/-- The expected arc lengths `t̄_α = Σ_{t_B} p(t_B) t_α`, (3.12): `meanLength D i j` is the
expected length of arc `(i, j)`. -/
noncomputable def meanLength (D : BundleDist n) (i j : Fin (n + 1)) : ℝ :=
  ∑ v ∈ D.supp j, D.p j v * v i

/-- The numbers `g_i` of (3.13): the critical path length to `i` for the expected arc lengths. -/
noncomputable def meanCPL (N : ProjectNetwork n) (D : BundleDist n) (i : Fin (n + 1)) : ℝ :=
  earliest N (meanLength D) i

/-- The numbers `f_j` of (4.2), p. 8: `f_origin = 0` and, for `j ≠ 0`,
`f_j = Σ_{v} p_j(v) · max_{i ∈ pred j} (f_i + v_i)`, the maximum over the arcs `(i, j)` that
exist (missing arcs ignored). Only the bundle distribution of event `j` enters at `j`. -/
noncomputable def fNum (N : ProjectNetwork n) (D : BundleDist n) (j : Fin (n + 1)) : ℝ :=
  if h : j = 0 then 0
  else ∑ v ∈ D.supp j, D.p j v *
    (N.pred j).attach.sup' (Finset.attach_nonempty_iff.2 (N.pred_nonempty h))
      (fun i => fNum N D i.1 + v i.1)
termination_by j.val
decreasing_by exact N.lt_of_mem_pred i.2

/-- The length of a path given as its list of nodes `v_0, …, v_k`: the sum of `y v_{r-1} v_r`. -/
def pathLength (y : Fin (n + 1) → Fin (n + 1) → ℝ) (p : List (Fin (n + 1))) : ℝ :=
  ((p.zip p.tail).map (fun e => y e.1 e.2)).sum

/-- `p` is a path (directed chain) of the network from the origin to the event `i`, listed by its
nodes. -/
def IsPathTo (N : ProjectNetwork n) (p : List (Fin (n + 1))) (i : Fin (n + 1)) : Prop :=
  p.head? = some 0 ∧ p.getLast? = some i ∧ p.IsChain (fun a b => (a, b) ∈ N.P)

/-- A joint finite distribution on all arc lengths (remark, p. 12): `supp` is a finite set of
length assignments `y` (`y i j` the length of arc `(i, j)`), and `p y` the probability of `y`. -/
structure JointDist (n : ℕ) where
  /-- The finite support of the joint distribution. -/
  supp : Finset (Fin (n + 1) → Fin (n + 1) → ℝ)
  /-- `p y` is the probability of the assignment `y`. -/
  p : (Fin (n + 1) → Fin (n + 1) → ℝ) → ℝ

/-- A joint distribution is a probability distribution on its finite support. -/
def JointDist.IsProb (J : JointDist n) : Prop :=
  (∀ y ∈ J.supp, 0 ≤ J.p y) ∧ ∑ y ∈ J.supp, J.p y = 1

/-- The expected critical path length to `i` under a joint distribution. -/
noncomputable def jointExpected (N : ProjectNetwork n) (J : JointDist n) (i : Fin (n + 1)) : ℝ :=
  ∑ y ∈ J.supp, J.p y * earliest N y i

/-- The expected length of arc `(i, j)` under a joint distribution. -/
noncomputable def jointMean (J : JointDist n) (i j : Fin (n + 1)) : ℝ :=
  ∑ y ∈ J.supp, J.p y * y i j

/-- The bundle marginals of a joint distribution: at event `j`, the law of the bundle vector
`fun i => y i j`. -/
noncomputable def JointDist.marginals (J : JointDist n) : BundleDist n where
  supp j := J.supp.image (fun y i => y i j)
  p j v := ∑ y ∈ J.supp with (fun i => y i j) = v, J.p y

end FulkersonPERT.Bounds
