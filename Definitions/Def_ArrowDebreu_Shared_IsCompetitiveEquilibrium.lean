import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy

namespace ArrowDebreu.Shared

variable {l m n : ℕ}

/-- **Condition 1** (§1.2.3, p. 268, PDF p. 5): `y_j^*` maximizes `p^*·y_j` over the set `Y_j`,
for each `j` — i.e. `y_j^* ∈ Y_j` and `p^*·y_j ≤ p^*·y_j^*` for every `y_j ∈ Y_j`. -/
def Condition1 (E : Economy l m n) (p : Fin l → ℝ) (y : Fin n → Fin l → ℝ) : Prop :=
  ∀ j, y j ∈ E.Y j ∧ ∀ y' ∈ E.Y j, p ⬝ᵥ y' ≤ p ⬝ᵥ y j

/-- The budget set `{x_i | x_i ∈ X_i, p·x_i ≦ p·ζ_i + Σ_{j=1}^n α_{ij} p·y_j}` of consumer `i`
(Condition 2, p. 271, PDF p. 8). -/
def budgetSet (E : Economy l m n) (p : Fin l → ℝ) (y : Fin n → Fin l → ℝ) (i : Fin m) :
    Set (Fin l → ℝ) :=
  {x | x ∈ E.X i ∧ p ⬝ᵥ x ≤ income E p y i}

/-- **Condition 2** (§1.3.3, p. 271, PDF p. 8): for each `i`, `x_i^*` maximizes `u_i(x_i)` over the
set `{x_i | x_i ∈ X_i, p^*·x_i ≦ p^*·ζ_i + Σ_{j=1}^n α_{ij} p^*·y_j^*}` — i.e. `x_i^*` belongs to
that set and `u_i(x_i) ≤ u_i(x_i^*)` for every `x_i` in it. -/
def Condition2 (E : Economy l m n) (p : Fin l → ℝ) (x : Fin m → Fin l → ℝ)
    (y : Fin n → Fin l → ℝ) : Prop :=
  ∀ i, x i ∈ budgetSet E p y i ∧ ∀ x' ∈ budgetSet E p y i, E.u i x' ≤ E.u i (x i)

/-- **Condition 3** (§1.4.0, p. 271, PDF p. 8): `p^* ∈ P = {p | p ∈ R^l, p ≧ 0, Σ_h p_h = 1}`. -/
def Condition3 (p : Fin l → ℝ) : Prop :=
  p ∈ priceSimplex l

/-- **Condition 4** (§1.4.1, p. 271, PDF p. 8): `z^* ≦ 0` (componentwise) and `p^*·z^* = 0`, where
`z = Σ_i x_i − Σ_j y_j − Σ_i ζ_i`. -/
def Condition4 (E : Economy l m n) (p : Fin l → ℝ) (x : Fin m → Fin l → ℝ)
    (y : Fin n → Fin l → ℝ) : Prop :=
  excessDemand E x y ≤ 0 ∧ p ⬝ᵥ excessDemand E x y = 0

/-- **Definition 1.5.0** (p. 272, PDF p. 9): a set of vectors `(x_1^*, ⋯, x_m^*, y_1^*, ⋯, y_n^*, p^*)`
is a *competitive equilibrium* if it satisfies Conditions 1–4. -/
def IsCompetitiveEquilibrium (E : Economy l m n) (x : Fin m → Fin l → ℝ)
    (y : Fin n → Fin l → ℝ) (p : Fin l → ℝ) : Prop :=
  Condition1 E p y ∧ Condition2 E p x y ∧ Condition3 p ∧ Condition4 E p x y

end ArrowDebreu.Shared
