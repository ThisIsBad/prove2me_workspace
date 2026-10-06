import Mathlib
import Definitions.Def_MulticlassQNet_FirstOrder_Network

namespace MulticlassQNet.FirstOrder

/-- A Markovian sequencing policy (§2, pp. 6–7): in state `n` (the vector of class populations)
it decides, as a function of the state only, which classes are in service. `serve n r = true`
is the event `B_r` that station `σ r` is serving a class-`r` job. Only a present job can be
served, and a single-server station serves at most one class at a time. Idling is allowed and
preemption is implicit (the decision is re-taken in every state). -/
structure Policy {N R : ℕ} (net : Network N R) where
  serve : (Fin R → ℕ) → Fin R → Bool
  serve_present : ∀ n r, serve n r = true → 1 ≤ n r
  serve_one_class : ∀ n r r', net.σ r = net.σ r' → r ≠ r' →
    ¬ (serve n r = true ∧ serve n r' = true)

/-- The unit vector `e_r`. -/
def unitVec {R : ℕ} (r : Fin R) : Fin R → ℕ := Pi.single r 1

/-- Mean number of class-`r` jobs under the distribution `π`, the paper's `n_r = λ_r x_r`. -/
noncomputable def meanNum {R : ℕ} (π : (Fin R → ℕ) → ℝ) (r : Fin R) : ℝ :=
  ∑' n, π n * (n r : ℝ)

namespace Policy

variable {N R : ℕ} {net : Network N R} (P : Policy net)

/-- The indicator `1{B_r}` of "station `σ r` busy with a class-`r` job" in state `n`. -/
def busy (n : Fin R → ℕ) (r : Fin R) : ℝ := if P.serve n r then 1 else 0

/-- The indicator `1{B_{0i}}` of "station `i` idle" in state `n`: no class of `C_i` is served
(whether or not jobs are waiting there). -/
def idle (i : Fin N) (n : Fin R → ℕ) : ℝ :=
  if ∀ r ∈ net.C i, P.serve n r = false then 1 else 0

/-- The generator of the continuous-time Markov chain `n(t)` under the policy, applied to a
test function `g`: arrivals of class `r` at rate `λ_{0r}`; if class `r` is served, a service
completion at rate `μ_r` that routes the job to class `s` w.p. `p_{rs}` or out w.p. `p_{r0}`. -/
noncomputable def generator (g : (Fin R → ℕ) → ℝ) (n : Fin R → ℕ) : ℝ :=
  ∑ r, net.lam0 r * (g (n + unitVec r) - g n) +
  ∑ r, P.busy n r * net.μ r *
    (∑ s, net.p r s * (g (n - unitVec r + unitVec s) - g n) +
      net.exitProb r * (g (n - unitVec r) - g n))

/-- `π` is an invariant distribution of the chain: a probability vector on the countable state
space satisfying global balance `πQ = 0` (the generator applied to the indicator of each
state `m` has `π`-mean zero). -/
def IsInvariant (π : (Fin R → ℕ) → ℝ) : Prop :=
  (∀ n, 0 ≤ π n) ∧ HasSum π 1 ∧
    ∀ m : Fin R → ℕ, HasSum (fun n => π n * P.generator (fun k => if k = m then 1 else 0) n) 0

/-- Assumption A (p. 7) for the policy, with `π` its invariant distribution:
(a) `π` is the unique invariant distribution; (b) `E_π[n_r²] < ∞` for every class `r`. -/
def AssumptionA (π : (Fin R → ℕ) → ℝ) : Prop :=
  P.IsInvariant π ∧ (∀ π', P.IsInvariant π' → π' = π) ∧
    ∀ r, Summable (fun n => π n * ((n r : ℝ)) ^ 2)

/-- `E_π[1{B_r}]`, the long-run fraction of time station `σ r` serves class `r`. -/
noncomputable def busyProb (π : (Fin R → ℕ) → ℝ) (r : Fin R) : ℝ :=
  ∑' n, π n * P.busy n r

/-- `I_{rr'} = E_π[1{B_r} n_{r'}]`, Eq. (22). -/
noncomputable def busyMoment (π : (Fin R → ℕ) → ℝ) (r r' : Fin R) : ℝ :=
  ∑' n, π n * P.busy n r * (n r' : ℝ)

/-- `N_{ir'} = E_π[1{B_{0i}} n_{r'}]`, Eq. (23). -/
noncomputable def idleMoment (π : (Fin R → ℕ) → ℝ) (i : Fin N) (r' : Fin R) : ℝ :=
  ∑' n, π n * P.idle i n * (n r' : ℝ)

end Policy

end MulticlassQNet.FirstOrder
