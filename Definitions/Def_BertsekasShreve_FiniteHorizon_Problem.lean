import Mathlib
import Definitions.Def_BertsekasShreve_FiniteHorizon_Model

namespace BertsekasShreve.FiniteHorizon

open Filter Topology

namespace Model

variable {S C : Type*} (m : Model S C)

/-- The `N`-stage cost function of the policy `π` with terminal function `J₀`,
`J_{N,π} = (T_{μ₀} T_{μ₁} ⋯ T_{μ_{N−1}})(J₀)`, eq. (5) of Chapter 2. -/
def costN (J₀ : S → EReal) (N : ℕ) (π : m.Policy) : S → EReal := m.comp π N J₀

/-- The `N`-stage optimal cost function `J*_N(x) = inf_{π ∈ Π} J_{N,π}(x)`, eq. (7) of
Chapter 2. The infimum is over policies, not over controls. -/
noncomputable def optCostN (J₀ : S → EReal) (N : ℕ) : S → EReal :=
  fun x => ⨅ π : m.Policy, m.costN J₀ N π x

/-- `π` is `N`-stage optimal: `J_{N,π} = J*_N` (p. 29). -/
def IsNStageOptimal (J₀ : S → EReal) (N : ℕ) (π : m.Policy) : Prop :=
  m.costN J₀ N π = m.optCostN J₀ N

/-- `π* = (μ₀*, μ₁*, …)` is uniformly `N`-stage optimal: the policy `(μ_i*, μ_{i+1}*, …)` is
`(N − i)`-stage optimal for every `i = 0, 1, …, N − 1` (p. 29). -/
def IsUniformlyNStageOptimal (J₀ : S → EReal) (N : ℕ) (π : m.Policy) : Prop :=
  ∀ i, i < N → m.IsNStageOptimal J₀ (N - i) (π.shift i)

/-- `π_ε` is `N`-stage `ε`-optimal (p. 29):
`J_{N,π_ε}(x) ≤ J*_N(x) + ε` if `J*_N(x) > −∞`, and `J_{N,π_ε}(x) ≤ −1/ε` if `J*_N(x) = −∞`. -/
def IsNStageEpsOptimal (J₀ : S → EReal) (N : ℕ) (ε : ℝ) (π : m.Policy) : Prop :=
  ∀ x, (m.optCostN J₀ N x ≠ ⊥ → m.costN J₀ N π x ≤ m.optCostN J₀ N x + (ε : EReal)) ∧
    (m.optCostN J₀ N x = ⊥ → m.costN J₀ N π x ≤ ((-(1 / ε) : ℝ) : EReal))

/-- The sequence of policies `{π_n}` exhibits `{ε_n}`-dominated convergence to optimality
(p. 29): `lim_{n→∞} J_{N,π_n} = J*_N` pointwise, and for `n = 2, 3, …`,
`J_{N,π_n}(x) ≤ J*_N(x) + ε_n` if `J*_N(x) > −∞`,
`J_{N,π_n}(x) ≤ J_{N,π_{n−1}}(x) + ε_n` if `J*_N(x) = −∞`.
Sequences are indexed by `n = 1, 2, …`; the entries at index `0` play no role. -/
def IsDominatedConvergence (J₀ : S → EReal) (N : ℕ) (ε : ℕ → ℝ) (πs : ℕ → m.Policy) : Prop :=
  (∀ x, Tendsto (fun n => m.costN J₀ N (πs n) x) atTop (𝓝 (m.optCostN J₀ N x))) ∧
    ∀ n, 2 ≤ n → ∀ x,
      (m.optCostN J₀ N x ≠ ⊥ → m.costN J₀ N (πs n) x ≤ m.optCostN J₀ N x + (ε n : EReal)) ∧
      (m.optCostN J₀ N x = ⊥ →
        m.costN J₀ N (πs n) x ≤ m.costN J₀ N (πs (n - 1)) x + (ε n : EReal))

end Model

end BertsekasShreve.FiniteHorizon
