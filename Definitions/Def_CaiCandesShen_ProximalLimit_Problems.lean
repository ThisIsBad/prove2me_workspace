import Mathlib
import Definitions.Def_CaiCandesShen_ProximalLimit_Basic

namespace CaiCandesShen.ProximalLimit

/-- `X` satisfies the constraints `f_i(X) ≤ 0`, `i = 1, …, m`, of (1.6) and (3.4)
(§1.3, p. 1959; §3.2, p. 1965): `X ∈ C = {X : f_i(X) ≤ 0 ∀ i = 1, …, m}`. -/
def Feasible {m n₁ n₂ : ℕ} (f : Fin m → Mat n₁ n₂ → ℝ) (X : Mat n₁ n₂) : Prop :=
  ∀ i, f i X ≤ 0

/-- `X` is a solution of problem (1.6) (§1.3, p. 1959):
`minimize ‖X‖_*  subject to  f_i(X) ≤ 0, i = 1, …, m`. -/
def IsNuclearNormSolution {m n₁ n₂ : ℕ} (f : Fin m → Mat n₁ n₂ → ℝ) (X : Mat n₁ n₂) : Prop :=
  Feasible f X ∧ ∀ X', Feasible f X' → nuclearNorm X ≤ nuclearNorm X'

/-- `X` is the minimum Frobenius norm solution of (1.6), eq. (3.14) (p. 1967):
`X_∞ := arg min_X {‖X‖_F² : X is a solution of (1.6)}`. -/
def IsMinFrobeniusSolution {m n₁ n₂ : ℕ} (f : Fin m → Mat n₁ n₂ → ℝ) (X : Mat n₁ n₂) : Prop :=
  IsNuclearNormSolution f X ∧
    ∀ X', IsNuclearNormSolution f X' → frobNorm X ^ 2 ≤ frobNorm X' ^ 2

/-- `X` is a solution of the proximal problem (3.4) (§3.2, p. 1965):
`minimize f_τ(X)  subject to  f_i(X) ≤ 0, i = 1, …, m`. -/
def IsProximalSolution {m n₁ n₂ : ℕ} (f : Fin m → Mat n₁ n₂ → ℝ) (τ : ℝ) (X : Mat n₁ n₂) :
    Prop :=
  Feasible f X ∧ ∀ X', Feasible f X' → fτ τ X ≤ fτ τ X'

end CaiCandesShen.ProximalLimit
