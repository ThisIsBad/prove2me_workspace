import Mathlib
import Definitions.Def_RobinsonSR_Reduction_Setting
import Definitions.Def_RobinsonSR_Schur_Setting

namespace RobinsonSR.NLP

open scoped Topology RealInnerProductSpace Matrix

/-! ### Generalized equations on a real inner-product space -/

/-- Strong regularity (DEFINITION, p. 45), stated on the data of the linearisation: `a` plays
`f(z₀)` and `A` plays `f′(z₀)`, so that `T z = a + A (z - z₀) + ∂ψ_C(z)`. The generalized equation
`0 ∈ f(z) + ∂ψ_C(z)` is strongly regular at `z₀` with associated Lipschitz constant `lam` if there
are neighbourhoods `U` of `0` and `V` of `z₀` such that the restriction to `U` of `T⁻¹ ∩ V` is a
single-valued function `s : U → V`, Lipschitzian on `U` with modulus `lam`: for every `y ∈ U`,
`s y ∈ V` solves `y ∈ T (s y)`, it is the only solution of `y ∈ T z` with `z ∈ V`, and
`‖s y₁ - s y₂‖ ≤ lam * ‖y₁ - y₂‖` for `y₁, y₂ ∈ U`. -/
def StronglyRegular {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (C : Set E) (a : E) (A : E →L[ℝ] E) (z0 : E) (lam : ℝ) : Prop :=
  ∃ U ∈ 𝓝 (0 : E), ∃ V ∈ 𝓝 z0, ∃ s : E → E,
    (∀ y ∈ U, s y ∈ V ∧ y - (a + A (s y - z0)) ∈ RobinsonSR.Reduction.normalCone C (s y) ∧
       ∀ z ∈ V, y - (a + A (z - z0)) ∈ RobinsonSR.Reduction.normalCone C z → z = s y) ∧
    ∀ y₁ ∈ U, ∀ y₂ ∈ U, ‖s y₁ - s y₂‖ ≤ lam * ‖y₁ - y₂‖

/-- The generalized equation `0 ∈ F(z) + ∂ψ_C(z)` is strongly regular at `z₀` (DEFINITION, p. 45):
`F` is Fréchet differentiable at `z₀`, with derivative `DF`, and the linearisation
`F(z₀) + DF (z - z₀) + ∂ψ_C(z)` is strongly regular at `z₀` for some Lipschitz constant `lam`. -/
def StronglyRegularAt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : E → E) (C : Set E) (z0 : E) : Prop :=
  ∃ DF : E →L[ℝ] E, HasFDerivAt F DF z0 ∧ ∃ lam : ℝ, StronglyRegular C (F z0) DF z0 lam

/-! ### The nonlinear program (4.1) and its KKT generalized equation (4.3) -/

/-- The gradient of the Lagrangian `ℒ(x, u, v) = θ(x) + ⟨u, g(x)⟩ + ⟨v, h(x)⟩` in `x` (p. 54):
`ℒ′(x, u, v) = ∇θ(x) + ∑ᵢ uᵢ ∇gᵢ(x) + ∑ⱼ vⱼ ∇hⱼ(x)`. -/
noncomputable def lagGrad {n p q : ℕ} (θ : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin p))
    (h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin q))
    (x : EuclideanSpace ℝ (Fin n)) (u : EuclideanSpace ℝ (Fin p)) (v : EuclideanSpace ℝ (Fin q)) :
    EuclideanSpace ℝ (Fin n) :=
  gradient θ x + ∑ i, u i • gradient (fun y => g y i) x + ∑ j, v j • gradient (fun y => h y j) x

/-- The Hessian of the Lagrangian in `x` at `(x₀, u₀, v₀)`, `ℒ″ = ℒ″(x₀, u₀, v₀)` (p. 54): the
Fréchet derivative at `x₀` of `x ↦ ℒ′(x, u₀, v₀)`. -/
noncomputable def lagHess {n p q : ℕ} (θ : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin p))
    (h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin q))
    (x0 : EuclideanSpace ℝ (Fin n)) (u0 : EuclideanSpace ℝ (Fin p)) (v0 : EuclideanSpace ℝ (Fin q)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  fderiv ℝ (fun x => lagGrad θ g h x u0 v0) x0

/-- The space `ℝⁿ × ℝᵖ × ℝ^q` of triples `z = (x, u, v)`, with the Euclidean norm and inner product
of `ℝ^{n+p+q}`. -/
abbrev KKTSpace (n p q : ℕ) : Type := EuclideanSpace ℝ (Fin n ⊕ (Fin p ⊕ Fin q))

/-- The `x`-component of `z = (x, u, v)`. -/
def xPart {n p q : ℕ} (z : KKTSpace n p q) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => z (Sum.inl i))

/-- The `u`-component of `z = (x, u, v)`. -/
def uPart {n p q : ℕ} (z : KKTSpace n p q) : EuclideanSpace ℝ (Fin p) :=
  WithLp.toLp 2 (fun i => z (Sum.inr (Sum.inl i)))

/-- The `v`-component of `z = (x, u, v)`. -/
def vPart {n p q : ℕ} (z : KKTSpace n p q) : EuclideanSpace ℝ (Fin q) :=
  WithLp.toLp 2 (fun j => z (Sum.inr (Sum.inr j)))

/-- The triple `(x, u, v)` as a point of `ℝⁿ × ℝᵖ × ℝ^q`. -/
def mk {n p q : ℕ} (x : EuclideanSpace ℝ (Fin n)) (u : EuclideanSpace ℝ (Fin p))
    (v : EuclideanSpace ℝ (Fin q)) : KKTSpace n p q :=
  WithLp.toLp 2 (Sum.elim (fun i => x i) (Sum.elim (fun i => u i) (fun j => v j)))

/-- The single-valued part of the generalized equation (4.3):
`F(x, u, v) = (ℒ′(x, u, v), −g(x), −h(x))`. -/
noncomputable def kktMap {n p q : ℕ} (θ : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin p))
    (h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin q)) :
    KKTSpace n p q → KKTSpace n p q :=
  fun z => mk (lagGrad θ g h (xPart z) (uPart z) (vPart z)) (-g (xPart z)) (-h (xPart z))

/-- The set `ℝⁿ × ℝᵖ₊ × ℝ^q` of (4.3): triples whose `u`-component is componentwise nonnegative. -/
def kktCone (n p q : ℕ) : Set (KKTSpace n p q) :=
  {z | ∀ i, 0 ≤ uPart z i}

/-! ### Matrices of §3–§4 -/

/-- `M` is a P-matrix (p. 52): every principal minor of `M` is positive, i.e. for every nonempty
index set `J` the principal submatrix `M[J, J]` has positive determinant. -/
def IsPMatrix {ι : Type*} [DecidableEq ι] (M : Matrix ι ι ℝ) : Prop :=
  ∀ J : Finset ι, J.Nonempty →
    0 < (M.submatrix (fun i : J => (i : ι)) (fun i : J => (i : ι))).det

/-- The matrix (4.5),
`[ℒ″ Hᵀ G⁺ᵀ; −H 0 0; −G⁺ 0 0]`, with `Q` playing `ℒ″`, `H` the `q × n` and `Gp` the `r × n` matrix. -/
def kktMatrix {ιn ιq ιr : Type*} (Q : Matrix ιn ιn ℝ) (H : Matrix ιq ιn ℝ) (Gp : Matrix ιr ιn ℝ) :
    Matrix (ιn ⊕ (ιq ⊕ ιr)) (ιn ⊕ (ιq ⊕ ιr)) ℝ :=
  Matrix.fromBlocks Q (Matrix.fromCols Hᵀ Gpᵀ) (Matrix.fromRows (-H) (-Gp)) 0

/-- The row block `[G⁰ 0 0]` of (4.6). -/
def zeroRowBlock {ιn ιq ιr ιs : Type*} (G0 : Matrix ιs ιn ℝ) :
    Matrix ιs (ιn ⊕ (ιq ⊕ ιr)) ℝ :=
  Matrix.fromCols G0 0

/-- The Schur complement (4.6): `S = [G⁰ 0 0] (4.5)⁻¹ [G⁰ 0 0]ᵀ`. It is meaningful only when the
matrix (4.5) is nonsingular (Mathlib's `⁻¹` of a singular matrix is `0`). -/
noncomputable def schurS {ιn ιq ιr ιs : Type*} [Fintype ιn] [Fintype ιq] [Fintype ιr]
    [DecidableEq ιn] [DecidableEq ιq] [DecidableEq ιr]
    (Q : Matrix ιn ιn ℝ) (H : Matrix ιq ιn ℝ) (Gp : Matrix ιr ιn ℝ) (G0 : Matrix ιs ιn ℝ) :
    Matrix ιs ιs ℝ :=
  zeroRowBlock (ιq := ιq) (ιr := ιr) G0 * (kktMatrix Q H Gp)⁻¹ *
    (zeroRowBlock (ιq := ιq) (ιr := ιr) G0)ᵀ

/-- The matrix of `ℒ″` in the standard basis: entry `(i, j)` is the `i`-th coordinate of
`ℒ″ eⱼ`, so that `hessMatrix … *ᵥ y = ℒ″ y`. -/
noncomputable def hessMatrix {n p q : ℕ} (θ : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin p))
    (h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin q))
    (x0 : EuclideanSpace ℝ (Fin n)) (u0 : EuclideanSpace ℝ (Fin p)) (v0 : EuclideanSpace ℝ (Fin q)) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => lagHess θ g h x0 u0 v0 (EuclideanSpace.single j 1) i

/-- The Jacobian `H = h′(x₀)`: the `q × n` matrix whose `j`-th row is `∇hⱼ(x₀)`. -/
noncomputable def eqJacobian {n q : ℕ} (h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin q))
    (x0 : EuclideanSpace ℝ (Fin n)) : Matrix (Fin q) (Fin n) ℝ :=
  Matrix.of fun j k => gradient (fun x => h x j) x0 k

/-- The Jacobian of the inequality constraints with index in `{i | P i}`: the matrix whose row `i`
is `∇gᵢ(x₀)`. With `P i := 0 < u₀ᵢ` it is `G⁺`, with `P i := gᵢ(x₀) = 0 ∧ u₀ᵢ = 0` it is `G⁰`. -/
noncomputable def ineqJacobian {n p : ℕ} (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin p))
    (x0 : EuclideanSpace ℝ (Fin n)) (P : Fin p → Prop) : Matrix {i // P i} (Fin n) ℝ :=
  Matrix.of fun i k => gradient (fun x => g x i) x0 k

end RobinsonSR.NLP
