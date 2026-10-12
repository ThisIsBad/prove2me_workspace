import Mathlib
import Definitions.Def_ManneLP_Equilibrium_Model

namespace ManneLP.Equilibrium

/-- A stationary randomized decision rule (§2: "mixed strategies are available"): `q i j` is the
conditional probability of producing `j` when the initial stock is `i`. It is nonnegative, vanishes
off the admissible pairs, and sums to one over the admissible actions at every stock level
`i ≤ T`. -/
def IsRule (M : Model) (q : ℕ → ℕ → ℝ) : Prop :=
  (∀ i j, 0 ≤ q i j) ∧ (∀ i j, (i, j) ∉ M.A → q i j = 0) ∧
    ∀ i, i ≤ M.T → ∑ j ∈ actions M i, q i j = 1

/-- The transition probability of the Markov chain of initial stocks under the rule `q`: from
initial stock `i`, produce `j` with probability `q i j`, then the next month's initial stock is the
terminal stock `max(0, i + j − n)`. -/
noncomputable def trans (M : Model) (q : ℕ → ℕ → ℝ) (i t : ℕ) : ℝ :=
  ∑ j ∈ actions M i, q i j * termProb M (i + j) t

/-- Statistical equilibrium (§3, (2)): `y` is a probability distribution on the stock levels
`0, …, T` that the chain of `q` leaves unchanged, i.e. the law `y'` of the terminal stock equals the
law `y` of the initial stock. It need not be unique. -/
def IsEquilibrium (M : Model) (q : ℕ → ℕ → ℝ) (y : ℕ → ℝ) : Prop :=
  (∀ i, i ≤ M.T → 0 ≤ y i) ∧ ∑ i ∈ states M, y i = 1 ∧
    ∀ t, t ≤ M.T → y t = ∑ i ∈ states M, y i * trans M q i t

/-- The joint law `xᵢⱼ = yᵢ q(j | i)` of initial stock and production quantity. -/
def jointLaw (y : ℕ → ℝ) (q : ℕ → ℕ → ℝ) : ℕ × ℕ → ℝ :=
  fun a => y a.1 * q a.1 a.2

/-- `ℰC₁(i)` under the joint law `x a · p n` of `(i, j, n)`. -/
noncomputable def expC₁ (M : Model) (x : ℕ × ℕ → ℝ) : ℝ :=
  ∑ a ∈ M.A, ∑' n : ℕ, x a * M.p n * M.C₁ a.1

/-- `ℰC₂(j)` under the joint law `x a · p n` of `(i, j, n)`. -/
noncomputable def expC₂ (M : Model) (x : ℕ × ℕ → ℝ) : ℝ :=
  ∑ a ∈ M.A, ∑' n : ℕ, x a * M.p n * M.C₂ a.2

/-- `ℰC₃(n − k)`, `k = i + j`, under the joint law `x a · p n` of `(i, j, n)`. -/
noncomputable def expC₃ (M : Model) (x : ℕ × ℕ → ℝ) : ℝ :=
  ∑ a ∈ M.A, ∑' n : ℕ, x a * M.p n * M.C₃ ((n : ℤ) - (a.1 : ℤ) - (a.2 : ℤ))

/-- The expected monthly cost (1), `ℰC₁(i) + ℰC₂(j) + ℰC₃(n − k)`, when `(i, j)` has law `x` on the
admissible pairs and the demand `n` is independent of `(i, j)` with law `p`. -/
noncomputable def expCost (M : Model) (x : ℕ × ℕ → ℝ) : ℝ :=
  expC₁ M x + expC₂ M x + expC₃ M x

/-- The expected monthly cost (1) of the rule `q` in the statistical equilibrium `y`. -/
noncomputable def eqCost (M : Model) (q : ℕ → ℕ → ℝ) (y : ℕ → ℝ) : ℝ :=
  expCost M (jointLaw y q)

end ManneLP.Equilibrium
