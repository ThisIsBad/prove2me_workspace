import Mathlib
import Definitions.Def_StochasticProg_Recourse_Instance

namespace StochasticProg.LShaped

open StochasticProg.Recourse
open scoped Matrix

variable {n1 n2 m1 m2 K : ℕ}

/-- `t ∈ pos W`: `t` is a nonnegative combination of the columns of the fixed recourse
matrix `W` (Birge & Louveaux, Ch. 3, p. 109 notation, used again in Ch. 5 Theorem 1). -/
def posW (inst : Instance n1 n2 m1 m2 K) (t : Fin m2 → ℝ) : Prop :=
  ∃ y : Fin n2 → ℝ, (∀ i, 0 ≤ y i) ∧ Matrix.mulVec inst.W y = t

/-- A basis of the second-stage subproblem (1.5), `min qᵀy s.t. Wy = h - Tx, y ≥ 0`: an
injective choice of `m2` of the `n2` columns of `W` (p. 220, "one of the finitely many
different bases of (1.5)"). `Fin m2 → Fin n2` is finite, so the injective ones are too —
this is the structural fact the finite-convergence proof rests on. -/
def Basis (n2 m2 : ℕ) : Type := {b : Fin m2 → Fin n2 // Function.Injective b}

noncomputable instance instFintypeBasis (n2 m2 : ℕ) : Fintype (Basis n2 m2) := by
  classical exact Subtype.fintype _

noncomputable instance instDecidableEqBasis (n2 m2 : ℕ) : DecidableEq (Basis n2 m2) := by
  classical exact Classical.decEq _

/-- The simplex multiplier a basis `b` of `W` determines for a second-stage cost vector
`q` : the standard simplex-tableau dual price `π = (W_bᵀ)⁻¹ q_b` of the basic solution `b`
(p. 219, "`πᵏν` the simplex multipliers"). Singular `W_b` (a non-basis choice) is sent to
the junk value `0` by `Matrix.inv`, never invoked once `b` is required to be optimal via
`IsOptimalAt` below. -/
noncomputable def multiplier (inst : Instance n1 n2 m1 m2 K) (b : Basis n2 m2)
    (q : Fin n2 → ℝ) : Fin m2 → ℝ :=
  Matrix.mulVec ((inst.W.submatrix id b.1)ᵀ)⁻¹ (fun j => q (b.1 j))

/-- The value basis `b` (for scenario `k`) claims at `x`: `πᵀ(h_k - T_k x)` (the two
displayed relations on p. 219, before Eq. (1.4)). -/
noncomputable def basisValue (inst : Instance n1 n2 m1 m2 K) (k : Fin K) (b : Basis n2 m2)
    (x : Fin n1 → ℝ) : ℝ :=
  dotProduct (multiplier inst b (inst.q k)) (inst.h k) -
    dotProduct (multiplier inst b (inst.q k)) (Matrix.mulVec (inst.T k) x)

noncomputable instance instFintypeBasisFun : Fintype (Fin K → Basis n2 m2) := by
  classical exact Pi.instFintype

noncomputable instance instDecidableEqBasisFun : DecidableEq (Fin K → Basis n2 m2) := by
  classical exact Classical.decEq _

/-- `β` (one basis per scenario) is a valid Step-3 witness at `x`: for every scenario `k`,
`β k` actually attains the true second-stage optimal value `Q(x, ξ_k)` — the content of LP
duality invoked on p. 219 ("`Q(xν, ξk) = (πνk)ᵀ(hk − Tkxν)`"). -/
def IsOptimalAt (inst : Instance n1 n2 m1 m2 K) (x : Fin n1 → ℝ) (β : Fin K → Basis n2 m2) :
    Prop :=
  ∀ k, (basisValue inst k (β k) x : EReal) = QVal inst x k

/-- The optimality-cut coefficients `(E, e)` of Eq. (1.6)-(1.7), built from a Step-3 witness
`β`, one basis per scenario. -/
noncomputable def optCutCoeffs (inst : Instance n1 n2 m1 m2 K) (β : Fin K → Basis n2 m2) :
    (Fin n1 → ℝ) × ℝ :=
  (fun i => ∑ k, inst.p k * dotProduct (multiplier inst (β k) (inst.q k)) (fun r => inst.T k r i),
   ∑ k, inst.p k * dotProduct (multiplier inst (β k) (inst.q k)) (inst.h k))

/-- A basis of the Step-2 feasibility-test LP (1.8)-(1.9): an injective choice of `m2`
columns of the extended matrix `[W | I | -I]` (its columns indexed by `y`-columns,
`v⁺`-columns and `v⁻`-columns respectively). -/
def FeasBasis (n2 m2 : ℕ) : Type :=
  {b : Fin m2 → (Fin n2 ⊕ Fin m2 ⊕ Fin m2) // Function.Injective b}

noncomputable instance instFintypeFeasBasis (n2 m2 : ℕ) : Fintype (FeasBasis n2 m2) := by
  classical exact Subtype.fintype _

noncomputable instance instDecidableEqFeasBasis (n2 m2 : ℕ) : DecidableEq (FeasBasis n2 m2) := by
  classical exact Classical.decEq _

/-- The extended constraint matrix `[W | I | -I]` of Eq. (1.9). -/
def feasMatrix (inst : Instance n1 n2 m1 m2 K) :
    Matrix (Fin m2) (Fin n2 ⊕ Fin m2 ⊕ Fin m2) ℝ :=
  fun i c => match c with
    | Sum.inl j => inst.W i j
    | Sum.inr (Sum.inl j) => if i = j then 1 else 0
    | Sum.inr (Sum.inr j) => if i = j then -1 else 0

/-- The extended objective `min eᵀv⁺ + eᵀv⁻` of Eq. (1.8): `0` on the `y`-columns, `1` on
the `v⁺`/`v⁻`-columns. -/
def feasCost : (Fin n2 ⊕ Fin m2 ⊕ Fin m2) → ℝ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr _) => 1

/-- The simplex multiplier a feasibility basis `b` determines: `σ = (([W|I|-I]_b)ᵀ)⁻¹ e_b`
(p. 220, "`σν` the associated simplex multipliers"). -/
noncomputable def feasMultiplier (inst : Instance n1 n2 m1 m2 K) (b : FeasBasis n2 m2) :
    Fin m2 → ℝ :=
  Matrix.mulVec (((feasMatrix inst).submatrix id b.1)ᵀ)⁻¹ (fun j => feasCost (b.1 j))

/-- The optimal value of the Step-2 feasibility-test LP (1.8)-(1.9) at `x` for scenario
`k`: always well-defined (the system is feasible for any `x`, taking `y = 0` and `v⁺, v⁻`
to absorb `h_k - T_k x`), nonnegative, and `0` exactly when scenario `k` is second-stage
feasible at `x`. -/
noncomputable def feasLPValue (inst : Instance n1 n2 m1 m2 K) (k : Fin K) (x : Fin n1 → ℝ) :
    ℝ :=
  sInf {w' : ℝ | ∃ y : Fin n2 → ℝ, ∃ vp vn : Fin m2 → ℝ,
    (∀ i, 0 ≤ y i) ∧ (∀ i, 0 ≤ vp i) ∧ (∀ i, 0 ≤ vn i) ∧
    Matrix.mulVec inst.W y + vp - vn = inst.h k - Matrix.mulVec (inst.T k) x ∧
    w' = (∑ i, vp i) + ∑ i, vn i}

/-- The value feasibility-basis `b` claims at `x` for scenario `k`: `σᵀ(h_k - T_k x)`
(Eq. (1.10)-(1.11), read as a value rather than as cut coefficients). -/
noncomputable def feasBasisValue (inst : Instance n1 n2 m1 m2 K) (k : Fin K) (b : FeasBasis n2 m2)
    (x : Fin n1 → ℝ) : ℝ :=
  dotProduct (feasMultiplier inst b) (inst.h k) -
    dotProduct (feasMultiplier inst b) (Matrix.mulVec (inst.T k) x)

/-- `b` is a valid Step-2 witness at `x` for scenario `k`: `b` actually attains the true
optimal value of the feasibility-test LP (1.8) there. -/
def IsFeasBasisOptimalAt (inst : Instance n1 n2 m1 m2 K) (k : Fin K) (b : FeasBasis n2 m2)
    (x : Fin n1 → ℝ) : Prop :=
  feasBasisValue inst k b x = feasLPValue inst k x

/-- The feasibility-cut coefficients `(D, d)` of Eq. (1.10)-(1.11), for scenario `k` and
witness basis `b`. -/
noncomputable def feasCutCoeffs (inst : Instance n1 n2 m1 m2 K) (k : Fin K) (b : FeasBasis n2 m2) :
    (Fin n1 → ℝ) × ℝ :=
  (fun i => dotProduct (feasMultiplier inst b) (fun r => inst.T k r i),
   dotProduct (feasMultiplier inst b) (inst.h k))

end StochasticProg.LShaped
