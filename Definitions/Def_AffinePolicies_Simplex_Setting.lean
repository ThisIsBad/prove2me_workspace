import Mathlib

namespace AffinePolicies.Simplex

open Matrix

variable {m n₁ n₂ : ℕ}

/-- `(x, y)` is feasible for `Π_Adapt(U)` (model (1)): `x ≥ 0` and, for every `b ∈ U`,
`y(b) ≥ 0` and `A x + B y(b) ≥ b` (componentwise). -/
def Feasible (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (U : Set (Fin m → ℝ)) (x : Fin n₁ → ℝ) (y : (Fin m → ℝ) → Fin n₂ → ℝ) : Prop :=
  0 ≤ x ∧ ∀ b ∈ U, 0 ≤ y b ∧ b ≤ A *ᵥ x + B *ᵥ y b

/-- `t` bounds the worst-case cost of `(x, y)` over `U`: `cᵀx + dᵀy(b) ≤ t` for every `b ∈ U`. -/
def CostLE (c : Fin n₁ → ℝ) (d : Fin n₂ → ℝ) (U : Set (Fin m → ℝ))
    (x : Fin n₁ → ℝ) (y : (Fin m → ℝ) → Fin n₂ → ℝ) (t : ℝ) : Prop :=
  ∀ b ∈ U, c ⬝ᵥ x + d ⬝ᵥ y b ≤ t

/-- `z_Adapt(U)`: the infimum of the worst-case costs achieved by feasible two-stage solutions. -/
noncomputable def zAdapt (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (c : Fin n₁ → ℝ) (d : Fin n₂ → ℝ) (U : Set (Fin m → ℝ)) : ℝ :=
  sInf {t | ∃ (x : Fin n₁ → ℝ) (y : (Fin m → ℝ) → Fin n₂ → ℝ),
    Feasible A B U x y ∧ CostLE c d U x y t}

/-- The affine second-stage policy `b ↦ P b + q`. -/
def affinePolicy (P : Matrix (Fin n₂) (Fin m) ℝ) (q : Fin n₂ → ℝ) :
    (Fin m → ℝ) → Fin n₂ → ℝ :=
  fun b => P *ᵥ b + q

/-- `z_Aff(U)`: the infimum of the worst-case costs achieved by feasible solutions whose
second stage is an affine policy. -/
noncomputable def zAff (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (c : Fin n₁ → ℝ) (d : Fin n₂ → ℝ) (U : Set (Fin m → ℝ)) : ℝ :=
  sInf {t | ∃ (x : Fin n₁ → ℝ) (P : Matrix (Fin n₂) (Fin m) ℝ) (q : Fin n₂ → ℝ),
    Feasible A B U x (affinePolicy P q) ∧ CostLE c d U x (affinePolicy P q) t}

/-- `(x, y)` is an optimal solution of `Π_Adapt(U)`: it is feasible, and every worst-case cost
bound achieved by any feasible two-stage solution is also achieved by `(x, y)`. -/
def IsOptimalAdapt (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (c : Fin n₁ → ℝ) (d : Fin n₂ → ℝ) (U : Set (Fin m → ℝ))
    (x : Fin n₁ → ℝ) (y : (Fin m → ℝ) → Fin n₂ → ℝ) : Prop :=
  Feasible A B U x y ∧
    ∀ (x' : Fin n₁ → ℝ) (y' : (Fin m → ℝ) → Fin n₂ → ℝ) (t : ℝ),
      Feasible A B U x' y' → CostLE c d U x' y' t → CostLE c d U x y t

/-- `(x, P, q)` is an optimal affine solution: it is feasible, and every worst-case cost bound
achieved by any feasible solution with an affine second stage is also achieved by it. -/
def IsOptimalAff (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (c : Fin n₁ → ℝ) (d : Fin n₂ → ℝ) (U : Set (Fin m → ℝ))
    (x : Fin n₁ → ℝ) (P : Matrix (Fin n₂) (Fin m) ℝ) (q : Fin n₂ → ℝ) : Prop :=
  Feasible A B U x (affinePolicy P q) ∧
    ∀ (x' : Fin n₁ → ℝ) (P' : Matrix (Fin n₂) (Fin m) ℝ) (q' : Fin n₂ → ℝ) (t : ℝ),
      Feasible A B U x' (affinePolicy P' q') → CostLE c d U x' (affinePolicy P' q') t →
        CostLE c d U x (affinePolicy P q) t

/-- The simplex `conv(b¹, …, b^{m+1})` spanned by the vertices `v`; the paper's `bʲ` is
`v (j - 1)` and `b^{m+1}` is `v (Fin.last m)`. -/
noncomputable def simplexSet (v : Fin (m + 1) → Fin m → ℝ) : Set (Fin m → ℝ) :=
  convexHull ℝ (Set.range v)

/-- `Q = [(b¹ − b^{m+1}) … (b^m − b^{m+1})]`: column `j` (0-based) is `v j − v (Fin.last m)`. -/
def Qmat (v : Fin (m + 1) → Fin m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j => v (Fin.castSucc j) i - v (Fin.last m) i

/-- `Y = [(g(b¹) − g(b^{m+1})) … (g(b^m) − g(b^{m+1}))]` for a second-stage map `g`
(display (2) with `g = y*`). -/
def Ymat (v : Fin (m + 1) → Fin m → ℝ) (g : (Fin m → ℝ) → Fin n₂ → ℝ) :
    Matrix (Fin n₂) (Fin m) ℝ :=
  Matrix.of fun i j => g (v (Fin.castSucc j)) i - g (v (Fin.last m)) i

/-- The affine interpolant `ỹ(b) = Y Q⁻¹ (b − b^{m+1}) + g(b^{m+1})` of the values of `g` at the
vertices of the simplex. -/
noncomputable def interpolant (v : Fin (m + 1) → Fin m → ℝ) (g : (Fin m → ℝ) → Fin n₂ → ℝ) :
    (Fin m → ℝ) → Fin n₂ → ℝ :=
  fun b => (Ymat v g * (Qmat v)⁻¹) *ᵥ (b - v (Fin.last m)) + g (v (Fin.last m))

end AffinePolicies.Simplex
