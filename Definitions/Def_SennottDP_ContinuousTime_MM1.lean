import Mathlib
import Definitions.Def_SennottDP_ContinuousTime_CTMDC

open scoped ENNReal NNReal
open Classical

namespace SennottDP.ContinuousTime

/-- Example 10.2.1 (pp. 242–243), service rate control of the M/M/1 queue, as a CTMDC with
states `i ∈ ℕ` (the number of customers) and actions the service rates `a ∈ ℝ`. Customers arrive
according to a Poisson process with rate `lam` (`λ`). In state `0` there is only the null action,
encoded as the rate `0`; in state `i ≥ 1` the action set is `rates` (`{a_1, …, a_K}`). There are
no instantaneous costs; the cost rates are (10.11): `g(0) = 0`, `g(i,a) = c(a) + H(i)` for
`i ≥ 1`, with `hold` the holding cost rate `H`. The transition rates and probabilities are
(10.12): `ν(0) = λ`, `P_{01} = 1`; for `i ≥ 1`, `ν(i,a) = λ + a`,
`P_{i,i+1}(a) = λ/(λ+a)`, `P_{i,i-1}(a) = a/(λ+a)`. -/
noncomputable def mm1 (lam : ℝ) (rates : Finset ℝ) (c : ℝ → ℝ) (hold : ℕ → ℝ) :
    CTMDC ℕ ℝ where
  A i := if i = 0 then {0} else rates
  G _ _ := 0
  g i a := if i = 0 then 0 else c a + hold i
  ν i a := if i = 0 then lam else lam + a
  P i a j :=
    if i = 0 then (if j = 1 then 1 else 0)
    else if j = i + 1 then ENNReal.ofReal (lam / (lam + a))
    else if j + 1 = i then ENNReal.ofReal (a / (lam + a))
    else 0

/-- The policy `d(a)` of §10.4 (p. 250) that always serves at rate `a ∈ rates` (and takes the
null action in state `0`), as a stationary policy of `mm1`. -/
noncomputable def mm1Serve (lam : ℝ) (rates : Finset ℝ) (c : ℝ → ℝ) (hold : ℕ → ℝ) (a : ℝ)
    (ha : a ∈ rates) : (mm1 lam rates c hold).Policy :=
  (mm1 lam rates c hold).ofStationary (fun i => if i = 0 then 0 else a) (by
    intro i
    by_cases h : i = 0 <;> simp [mm1, h, ha])

end SennottDP.ContinuousTime
