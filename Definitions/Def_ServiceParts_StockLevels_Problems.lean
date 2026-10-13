import Mathlib
import Definitions.Def_ServiceParts_StockLevels_Basic
import Definitions.Def_ServiceParts_StockLevels_CompoundPoissonDemand

namespace ServiceParts.StockLevels

/-! Problem 4 (3.40): minimize expected backorders subject to an investment budget. -/

/-- Average investment in on-hand inventory of a vector of stock levels,
`Σ_i c_i [s_i - µ_i + B_i(s_i)]` (Muckstadt 2005, p. 60, (3.40); `C(θ)` of p. 61 is this
quantity at `s = s*(θ)`). -/
noncomputable def totalInvestment {ι : Type*} [Fintype ι] (d : ι → CompoundPoissonDemand)
    (c : ι → ℝ) (s : ι → ℕ) : ℝ :=
  ∑ i, c i * ((s i : ℝ) - (d i).mu + (d i).backorders (s i))

/-- Total expected backorders `Σ_i B_i(s_i)`, the objective of Problem 4 (3.40). -/
noncomputable def totalBackorders {ι : Type*} [Fintype ι] (d : ι → CompoundPoissonDemand)
    (s : ι → ℕ) : ℝ :=
  ∑ i, (d i).backorders (s i)

/-- The single-item Lagrangian cost `f(s) = (1 + θc) B(s) + θ c s` (Muckstadt 2005, p. 61). -/
noncomputable def relaxedCost (d : CompoundPoissonDemand) (c θ : ℝ) (s : ℕ) : ℝ :=
  (1 + θ * c) * d.backorders s + θ * c * s

/-- The stock levels meeting the criterion of p. 61, `Σ_{x ≤ s} p(x|µ) ≥ 1/(1 + θc)`;
the book's `s*(θ)` is the least element of this set. -/
def stockSet (d : CompoundPoissonDemand) (c θ : ℝ) : Set ℕ :=
  {s | 1 / (1 + θ * c) ≤ d.readyRate s}

/-- `θ` at which `p(0|µ) = 1/(1 + θc)`, namely `(1/c)(1/p(0|µ) - 1)` (Muckstadt 2005, p. 63). -/
noncomputable def thetaZero (d : CompoundPoissonDemand) (c : ℝ) : ℝ :=
  1 / c * (1 / d.pmf 0 - 1)

/-! Problem 5 (3.41): maximize the average fill rate under simple Poisson demand. -/

/-- Average expected system fill rate `Σ_i (λ_i / Σ_j λ_j) F_i(s_i)` with
`F_i(s) = Σ_{x < s} p(x|λ_i τ̄_i)` (Muckstadt 2005, p. 64, (3.41)). -/
noncomputable def avgFillRate {ι : Type*} [Fintype ι] (lam tbar : ι → ℝ) (s : ι → ℕ) : ℝ :=
  ∑ i, lam i / (∑ j, lam j) * poissonFillRate (lam i * tbar i) (s i)

/-- Marginal fill-rate gain per dollar
`Δ_i(s_i) = (λ_i / Σ_j λ_j) (F_i(s_i + 1) - F_i(s_i)) / c_i` (Muckstadt 2005, p. 65). -/
noncomputable def greedyRatio {ι : Type*} [Fintype ι] (lam tbar c : ι → ℝ) (i : ι) (si : ℕ) : ℝ :=
  lam i / (∑ j, lam j) *
    ((poissonFillRate (lam i * tbar i) (si + 1) - poissonFillRate (lam i * tbar i) si) / c i)

/-- A run of the greedy (marginal analysis) procedure of p. 65: start at
`s_i = ⌊λ_i τ̄_i⌋` and, at every step, increase by one unit the stock level of an item
`i*` maximizing `Δ_i(s_i)` (ties broken arbitrarily). `seq k` is the vector after `k` steps. -/
def IsGreedySeq {ι : Type*} [Fintype ι] [DecidableEq ι] (lam tbar c : ι → ℝ)
    (seq : ℕ → ι → ℕ) : Prop :=
  (∀ i, seq 0 i = ⌊lam i * tbar i⌋₊) ∧
    ∀ k, ∃ istar : ι,
      (∀ i, greedyRatio lam tbar c i (seq k i) ≤ greedyRatio lam tbar c istar (seq k istar)) ∧
      seq (k + 1) = Function.update (seq k) istar (seq k istar + 1)

end ServiceParts.StockLevels
