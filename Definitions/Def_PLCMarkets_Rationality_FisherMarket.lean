import Mathlib

namespace PLCMarkets.Rationality

/-- A nondecreasing, concave, piecewise-linear function `f : ℝ₊ → ℝ₊` with `f 0 = 0` and rational
data (Vazirani–Yannakakis 2011, §2, pp. 10:6–10:7; the last, unbounded piece is "the last
(infinite) segment of `f^i_j`" of §6, p. 10:10).

The bounded segments are listed from the origin: `segs = [(c₁, a₁), (c₂, a₂), …, (c_m, a_m)]`
means that `f` has slope `c₁` on `[0, a₁]`, slope `c₂` on `[a₁, a₁ + a₂]`, and so on (a pair is
`(slope, amount)`); beyond `a₁ + ⋯ + a_m` the function has slope `tail` forever (`tail = 0`: `f`
is flat there). Slopes are nonnegative (`f` is nondecreasing), amounts are positive, and slopes
are nonincreasing along the list and down to `tail` (`f` is concave). -/
structure PLConcave where
  /-- The segments, as `(slope, amount)` pairs, in order from the origin. -/
  segs : List (ℚ × ℚ)
  slope_nonneg : ∀ s ∈ segs, 0 ≤ s.1
  amount_pos : ∀ s ∈ segs, 0 < s.2
  slope_antitone : segs.Pairwise (fun s t => t.1 ≤ s.1)
  /-- The slope of the last, unbounded piece `[a₁ + ⋯ + a_m, ∞)`. -/
  tail : ℚ
  tail_nonneg : 0 ≤ tail
  tail_le : ∀ s ∈ segs, tail ≤ s.1

/-- Evaluation of the piecewise-linear function with segments `segs` at the point `x`
(negative `x` is treated as `0`):
`f(x) = Σ_k c_k · min(max(x − a₁ − ⋯ − a_{k−1}, 0), a_k)`. -/
noncomputable def plEval : List (ℚ × ℚ) → ℝ → ℝ
  | [], _ => 0
  | (c, a) :: rest, x => (c : ℝ) * min (max x 0) (a : ℝ) + plEval rest (x - (a : ℝ))

/-- The value `f(x)` of a piecewise-linear concave function: the bounded segments, plus the
unbounded last piece of slope `tail` beyond `a₁ + ⋯ + a_m`. -/
noncomputable def PLConcave.eval (f : PLConcave) (x : ℝ) : ℝ :=
  plEval f.segs x + (f.tail : ℝ) * max (x - (((f.segs.map Prod.snd).sum : ℚ) : ℝ)) 0

/-- A Fisher market with `n` buyers (`Fin n`) and `g` divisible goods (`Fin g`), one unit of each
good, rational positive budgets `e(i)`, and additively separable piecewise-linear concave
utilities: `f^i_j` is `util i j` (Vazirani–Yannakakis 2011, §2, p. 10:6). -/
structure FisherMarket (n g : ℕ) where
  /-- The money `e(i)` of buyer `i`. -/
  budget : Fin n → ℚ
  budget_pos : ∀ i, 0 < budget i
  /-- `util i j` is the function `f^i_j` giving buyer `i`'s utility from good `j`. -/
  util : Fin n → Fin g → PLConcave

namespace FisherMarket

variable {n g : ℕ}

/-- Buyer `i`'s utility `u_i(x) = Σ_j f^i_j(x_j)` for a bundle `x`. -/
noncomputable def utility (M : FisherMarket n g) (i : Fin n) (x : Fin g → ℝ) : ℝ :=
  ∑ j, (M.util i j).eval (x j)

/-- `x` is an optimal bundle (a utility-maximizing bundle in the budget set) for buyer `i`
at prices `p`: `x ≥ 0`, `Σ_j p_j x_j ≤ e(i)`, and no bundle `y ≥ 0` with
`Σ_j p_j y_j ≤ e(i)` gives `i` more utility. -/
def IsOptimalBundle (M : FisherMarket n g) (p : Fin g → ℝ) (i : Fin n) (x : Fin g → ℝ) : Prop :=
  (∀ j, 0 ≤ x j) ∧ ∑ j, p j * x j ≤ (M.budget i : ℝ) ∧
    ∀ y : Fin g → ℝ, (∀ j, 0 ≤ y j) → ∑ j, p j * y j ≤ (M.budget i : ℝ) →
      M.utility i y ≤ M.utility i x

/-- `p` are equilibrium (market clearing) prices (Vazirani–Yannakakis 2011, §2, p. 10:6): prices
are nonnegative, and there is an allocation giving every buyer an optimal bundle such that
every good is exactly cleared (its unit supply is fully sold). -/
def IsEquilibrium (M : FisherMarket n g) (p : Fin g → ℝ) : Prop :=
  (∀ j, 0 ≤ p j) ∧
    ∃ x : Fin n → Fin g → ℝ, (∀ i, M.IsOptimalBundle p i (x i)) ∧ ∀ j, ∑ i, x i j = 1

end FisherMarket

end PLCMarkets.Rationality
