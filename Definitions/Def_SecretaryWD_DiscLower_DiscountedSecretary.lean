import Mathlib

namespace SecretaryWD.DiscLower

open Finset

/-- A randomized online stopping rule for the discounted secretary problem with `n` arrivals
(Babaioff et al., SODA 2009, §2, pp. 3–4).

Times are `Fin n`; index `t` is the paper's time `t + 1`. The argument `h : Fin n → ℝ` is the
sequence of values in arrival order, `h s = v (π s)`. If the rule has not stopped before time
`t`, it stops at `t` (selecting the element arriving at `t`) with probability `stop t h`.
`adapted` says this probability depends only on the values observed up to and including time
`t`: the rule observes values only, online, and never looks ahead. The rule may depend on the
horizon `n` and the discount function (fixed inputs), but it is not given the instance. -/
structure StoppingRule (n : ℕ) where
  /-- probability of stopping at time `t`, given the arrival-ordered values `h` -/
  stop : Fin n → (Fin n → ℝ) → ℝ
  stop_nonneg : ∀ t h, 0 ≤ stop t h
  stop_le_one : ∀ t h, stop t h ≤ 1
  adapted : ∀ (t : Fin n) (h h' : Fin n → ℝ), (∀ s, s ≤ t → h s = h' s) → stop t h = stop t h'

/-- The values in arrival order under the order `π` (read *time ↦ element*):
the element `π t` arrives at time `t`. -/
def arrivalValues {n : ℕ} (v : Fin n → ℝ) (π : Equiv.Perm (Fin n)) : Fin n → ℝ :=
  fun t => v (π t)

/-- Probability that the rule `A` stops exactly at time `t` on the arrival-ordered values `h`:
`p_t(h) · ∏_{s < t} (1 − p_s(h))`. -/
def stopProb {n : ℕ} (A : StoppingRule n) (h : Fin n → ℝ) (t : Fin n) : ℝ :=
  A.stop t h * ∏ s ∈ univ.filter (fun s => s < t), (1 - A.stop s h)

/-- Expected discounted value `E_π[d(π⁻¹(e_A)) · v(e_A)]` of the rule `A` on values `v` with
discount `d`, the order `π` uniform over all `n!` permutations. Selecting nothing earns `0`. -/
noncomputable def expectedValue {n : ℕ} (d v : Fin n → ℝ) (A : StoppingRule n) : ℝ :=
  (1 / (n.factorial : ℝ)) * ∑ π : Equiv.Perm (Fin n), ∑ t : Fin n,
    d t * v (π t) * stopProb A (arrivalValues v π) t

/-- Expected offline optimum `E_π[max_e d(π⁻¹(e)) · v(e)] = E_π[max_t d(t) · v(π(t))]`, the order
`π` uniform. (The supremum is over the finite type `Fin n`; it is a maximum for `n ≥ 1`.) -/
noncomputable def expectedOPT {n : ℕ} (d v : Fin n → ℝ) : ℝ :=
  (1 / (n.factorial : ℝ)) * ∑ π : Equiv.Perm (Fin n), ⨆ t : Fin n, d t * v (π t)

/-- Probability, over the uniform order and the rule's randomness, that `A` selects an element
among the first `m` arrivals (paper times `1, …, m`, i.e. indices `t < m`). -/
noncomputable def stopByProb {n : ℕ} (v : Fin n → ℝ) (A : StoppingRule n) (m : ℕ) : ℝ :=
  (1 / (n.factorial : ℝ)) * ∑ π : Equiv.Perm (Fin n),
    ∑ t ∈ univ.filter (fun t : Fin n => t.val < m), stopProb A (arrivalValues v π) t

end SecretaryWD.DiscLower
