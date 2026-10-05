import Mathlib
import Definitions.Def_SeatInventory_Distinct_DemandModel

namespace SeatInventory.Distinct

/-- The index set of the decision variables `X_ik` of the linear program (4.5) (Belobaba 1987,
pp. 88–90): pairs `(i, k)` of a fare class `i` and a seat number `k ∈ {1, …, n}`, `n` being the
capacity of the leg. -/
def seatPairs (ι : Type*) [Fintype ι] (n : ℕ) : Finset (ι × ℕ) :=
  Finset.univ ×ˢ Finset.Icc 1 n

/-- `m_i(k) = f_i · P[r_i ≥ k]`, the expected marginal revenue from selling the `k`-th seat in
class `i` (p. 90): the average fare of class `i` times the probability of selling `k` or more
seats in that class. -/
noncomputable def marginalRevenue {ι : Type*} (f : ι → ℝ) (d : ι → PMF ℕ) (x : ι × ℕ) : ℝ :=
  emsr (f x.1) (d x.1) x.2

/-- `T` is a set of `n` largest values of `m` among the elements of `D`: `T ⊆ D`, `|T| = n`, and
every value of `m` on `T` is at least every value of `m` on `D \ T`. With ties several such `T`
exist. -/
def IsTopN {α : Type*} (m : α → ℝ) (D T : Finset α) (n : ℕ) : Prop :=
  T ⊆ D ∧ T.card = n ∧ ∀ x ∈ T, ∀ y ∈ D, y ∉ T → m y ≤ m x

/-- The booking limits read off a set `T` of (class, seat) pairs: class `i` receives
`S_i = #{k : (i, k) ∈ T}` seats. -/
def allocationOf {ι : Type*} [DecidableEq ι] (T : Finset (ι × ℕ)) (i : ι) : ℕ :=
  (T.filter (fun x => x.1 = i)).card

/-- Feasibility for the linear program (4.5), p. 90, over the variables `X a`, `a ∈ D`:
`0 ≤ X a ≤ 1` and `Σ_{a ∈ D} X a ≤ n`. -/
def IsLPFeasible {α : Type*} (D : Finset α) (n : ℕ) (X : α → ℝ) : Prop :=
  (∀ a ∈ D, 0 ≤ X a ∧ X a ≤ 1) ∧ ∑ a ∈ D, X a ≤ (n : ℝ)

/-- The objective `Σ_{a ∈ D} X a · m a` of the linear program (4.5), p. 90. -/
noncomputable def lpObjective {α : Type*} (m : α → ℝ) (D : Finset α) (X : α → ℝ) : ℝ :=
  ∑ a ∈ D, X a * m a

end SeatInventory.Distinct
