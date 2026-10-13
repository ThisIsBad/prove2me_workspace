import Mathlib
import Definitions.Def_ServiceParts_Palm_ResupplySystem

open MeasureTheory ProbabilityTheory

namespace ServiceParts.Palm

/-- The compound Poisson (s–1, s) backorder system of Muckstadt (2005), Section 3.1, pp. 41–47:
the system of `ResupplySystem`, where in addition the `k`-th customer order asks for
`size k ≥ 1` units, order sizes are i.i.d., and all interarrival times, resupply times and order
sizes are mutually independent. All units of one order share the order's resupply time
`resupply k`. -/
structure CompoundResupplySystem (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω)
    extends ResupplySystem Ω P where
  /-- number of units asked for by the `k`-th customer order -/
  size : ℕ → Ω → ℕ
  size_measurable : ∀ k, Measurable (size k)
  /-- every order asks for at least one unit -/
  size_pos : ∀ k ω, 1 ≤ size k ω
  /-- order sizes are identically distributed -/
  size_law : ∀ k, P.map (size k) = P.map (size 0)
  /-- interarrival times, resupply times and order sizes are all mutually independent -/
  indep_all : iIndepFun (Sum.elim gap (Sum.elim resupply (fun k ω => (size k ω : ℝ)))) P

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The order-size probabilities `u_j = P[X_k = j]`. -/
noncomputable def CompoundResupplySystem.sizePMF (S : CompoundResupplySystem Ω P) (j : ℕ) : ℝ :=
  (P {ω | S.size 0 ω = j}).toReal

/-- The number of units in resupply at time `t`: the total size of the orders placed by time `t`
whose (common) resupply is not complete at time `t` (`0` on the null event where infinitely many
orders qualify). -/
noncomputable def CompoundResupplySystem.unitsInResupply (S : CompoundResupplySystem Ω P)
    (t : ℝ) (ω : Ω) : ℕ :=
  ∑ᶠ k ∈ {k : ℕ | S.arrival k ω ≤ t ∧ t < S.arrival k ω + S.resupply k ω}, S.size k ω

/-- The number of units in resupply at time `t` that have been in the resupply system for at
least `T` time units: the total size of the orders placed by time `t - T` whose resupply is not
complete at time `t`. -/
noncomputable def CompoundResupplySystem.agedUnitsInResupply (S : CompoundResupplySystem Ω P)
    (T t : ℝ) (ω : Ω) : ℕ :=
  ∑ᶠ k ∈ {k : ℕ | S.arrival k ω + T ≤ t ∧ t < S.arrival k ω + S.resupply k ω}, S.size k ω

/-- The `j`-fold convolution `u^{(j)}_n` of a probability vector `u` on `ℕ`: the probability that
`j` independent orders with size law `u` ask for `n` units in total. -/
noncomputable def convPow (u : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, n => if n = 0 then 1 else 0
  | j + 1, n => ∑ m ∈ Finset.range (n + 1), convPow u j m * u (n - m)

/-- The compound Poisson probabilities with Poisson parameter `μ` and compounding law `u`
(with `u 0 = 0`): `p(n | μ) = ∑_{y=0}^{n} e^{-μ} μ^y / y! · u^{(y)}_n`. -/
noncomputable def compoundPoissonPMF (μ : ℝ) (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ y ∈ Finset.range (n + 1), Real.exp (-μ) * μ ^ y / (Nat.factorial y : ℝ) * convPow u y n

end ServiceParts.Palm
