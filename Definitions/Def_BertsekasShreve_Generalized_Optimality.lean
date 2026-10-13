import Mathlib
import Definitions.Def_BertsekasShreve_Generalized_Model

namespace BertsekasShreve.Generalized

open Filter Topology

namespace Model

variable {S C : Type*} (P : Model S C)

/-- `π* ∈ Π̃` is `N`-stage optimal if `J_{N,π*} = J*_N` (p. 29). -/
def IsNStageOptimal (N : ℕ) (π : P.Policy) : Prop := P.JN N π = P.JNstar N

/-- `π* = (μ₀*, μ₁*, …)` is uniformly `N`-stage optimal if `(μ_i*, μ_{i+1}*, …)` is
`(N − i)`-stage optimal for all `i = 0, 1, …, N − 1` (p. 29). -/
def IsUniformlyNStageOptimal (N : ℕ) (π : P.Policy) : Prop :=
  ∀ i, i < N → P.IsNStageOptimal (N - i) (P.shift π i)

/-- `π ∈ Π̃` is optimal at `x ∈ S` if `J_π(x) = J*(x)` (p. 29). -/
def IsOptimalAt (π : P.Policy) (x : S) : Prop := P.Jpi π x = P.Jstar x

/-- `π* ∈ Π̃` is optimal if `J_{π*} = J*` (p. 29). -/
def IsOptimal (π : P.Policy) : Prop := P.Jpi π = P.Jstar

/-- Given `ε > 0`, `π_ε ∈ Π̃` is `N`-stage `ε`-optimal (p. 29) if for all `x`,
`J_{N,π_ε}(x) ≤ J*_N(x) + ε` when `J*_N(x) > −∞` and `J_{N,π_ε}(x) ≤ −1/ε` when `J*_N(x) = −∞`. -/
def IsNStageEpsOptimal (N : ℕ) (ε : ℝ) (π : P.Policy) : Prop :=
  ∀ x, (⊥ < P.JNstar N x → P.JN N π x ≤ P.JNstar N x + (ε : EReal)) ∧
    (P.JNstar N x = ⊥ → P.JN N π x ≤ ((-1 / ε : ℝ) : EReal))

/-- `{ε_n}`-dominated convergence to optimality (p. 29). For a sequence of positive numbers
`ε_n ↓ 0`, a sequence of policies `{π_n}` exhibits it if `lim_{n → ∞} J_{N,π_n} = J*_N`
(pointwise in `[−∞, ∞]`) and, for `n = 2, 3, …`,
`J_{N,π_n}(x) ≤ J*_N(x) + ε_n` if `J*_N(x) > −∞` and
`J_{N,π_n}(x) ≤ J_{N,π_{n−1}}(x) + ε_n` if `J*_N(x) = −∞`.
The book's index `n = 1, 2, …` is Lean's `k = n − 1`: `πs k = π_{k+1}`, `ε k = ε_{k+1}`; the
condition "for `n = 2, 3, …`" is the condition on `k + 1` for every `k`. -/
def DominatedConvergence (N : ℕ) (ε : ℕ → ℝ) (πs : ℕ → P.Policy) : Prop :=
  (∀ x, Tendsto (fun k => P.JN N (πs k) x) atTop (𝓝 (P.JNstar N x))) ∧
  ∀ k x,
    (⊥ < P.JNstar N x → P.JN N (πs (k + 1)) x ≤ P.JNstar N x + (ε (k + 1) : EReal)) ∧
    (P.JNstar N x = ⊥ → P.JN N (πs (k + 1)) x ≤ P.JN N (πs k) x + (ε (k + 1) : EReal))

end Model

end BertsekasShreve.Generalized
