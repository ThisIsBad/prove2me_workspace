import Mathlib

namespace SeatInventory.Distinct

/-- `P̄(S) = P[r ≥ S]`, the probability that the number of requests `r` of a fare class, with
law `p` on `ℕ`, is at least `S` (Belobaba 1987, Eq. (6.2), p. 142; the prose of Eq. (5.11),
p. 105: "the probability of selling `S` or more seats"). Requests are integer valued. -/
noncomputable def tailProb (p : PMF ℕ) (S : ℕ) : ℝ :=
  (p.toOuterMeasure (Set.Ici S)).toReal

/-- Expected bookings `b̄(S) = E[min(r, S)]` of a distinct fare-class inventory holding `S` seats
(Eqs. (5.3)–(5.4), p. 103): `r` requests are booked up to the `S` seats allocated. The summand is
bounded by `S · p(r)`, so the series always converges. -/
noncomputable def expectedBookings (p : PMF ℕ) (S : ℕ) : ℝ :=
  ∑' r : ℕ, (p r).toReal * ((min r S : ℕ) : ℝ)

/-- Expected spill `l̄(S) = E[(r − S)⁺]`, the expected number of refused requests
(Eqs. (5.3), (5.5), p. 103). `r - S` is truncated subtraction on `ℕ`, i.e. `(r − S)⁺`.
If `r` has infinite mean the series diverges and Lean's `tsum` returns `0`; every theorem using
this quantity assumes a finite mean. -/
noncomputable def expectedSpill (p : PMF ℕ) (S : ℕ) : ℝ :=
  ∑' r : ℕ, (p r).toReal * ((r - S : ℕ) : ℝ)

/-- Expected number of requests `r̄ = E[r]` (p. 103). Meaningful when the mean is finite; every
theorem using it assumes `Summable (fun r => (p r).toReal * r)`. -/
noncomputable def meanRequests (p : PMF ℕ) : ℝ :=
  ∑' r : ℕ, (p r).toReal * (r : ℝ)

/-- Expected revenue `R̄_i(S) = f_i · b̄_i(S)` of one fare class with average fare `f` and request
law `p`, holding `S` seats (Eq. (5.9), p. 105). -/
noncomputable def expectedRevenue (f : ℝ) (p : PMF ℕ) (S : ℕ) : ℝ :=
  f * expectedBookings p S

/-- Total expected revenue `R̄ = Σ_i R̄_i(S_i)` of a flight leg whose seats are split into
distinct (non-nested) inventories `S i`, one per fare class `i` (Eq. (5.9), p. 105);
`f i` is the average fare and `d i` the law of the requests of class `i`. -/
noncomputable def totalExpectedRevenue {ι : Type*} [Fintype ι] (f : ι → ℝ) (d : ι → PMF ℕ)
    (S : ι → ℕ) : ℝ :=
  ∑ i, expectedRevenue (f i) (d i) (S i)

/-- Expected marginal seat revenue of the `S`-th seat, `EMSR(S) = f · P̄(S) = f · P[r ≥ S]`
(Eq. (5.11), p. 105; Eqs. (6.1)–(6.2), p. 142); for `S ≥ 1` it is the `m_i(S)` of p. 90. -/
noncomputable def emsr (f : ℝ) (p : PMF ℕ) (S : ℕ) : ℝ :=
  f * tailProb p S

end SeatInventory.Distinct
