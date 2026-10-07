import Mathlib
import Definitions.Def_Gomory69_MasterFaces_GroupPolyhedron

namespace Gomory69.MasterFaces

/-- A linear row evaluated at its variable vector. -/
def rowEval {κ : Type*} [Fintype κ] (a x : κ → ℝ) : ℝ :=
  ∑ k, a k * x k

/-- A basic feasible solution of equations and inequalities: it satisfies every row,
and the coefficient vectors of all tight rows span the full variable space. -/
def IsBasicFeasible {ι κ : Type*} [Fintype κ]
    (a : ι → κ → ℝ) (b : ι → ℝ) (equation : Set ι) (x : κ → ℝ) : Prop :=
  (∀ r : ι, (r ∈ equation → rowEval (a r) x = b r) ∧
    (r ∉ equation → b r ≤ rowEval (a r) x)) ∧
  Submodule.span ℝ (a '' {r : ι | rowEval (a r) x = b r}) = ⊤

/-- The infinite system of Theorem 7 has one inequality for each integer solution. -/
def IsTBasicFeasible {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (N : Finset G) (g₀ : G) (π₀ : ℝ) (π : N → ℝ) : Prop :=
  IsBasicFeasible
    (fun t : {t : N → ℕ // GroupSolution N g₀ t} => castSolution t.val)
    (fun _ => π₀) (∅ : Set {t : N → ℕ // GroupSolution N g₀ t}) π

/-- A row of Gomory's finite system (13). The pair row is ordered, including equal entries. -/
inductive Row13 (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] (g₀ : G) where
  | target : Row13 G g₀
  | complement : (g : MasterIndex G) → (g : G) ≠ g₀ → Row13 G g₀
  | subadd : MasterIndex G → MasterIndex G → Row13 G g₀
  | nonnegative : MasterIndex G → Row13 G g₀

/-- The coefficient vector for evaluation at a group element; at zero it vanishes. -/
def coord {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (h : G) : MasterIndex G → ℝ :=
  fun g => if (g : G) = h then 1 else 0

/-- Coefficient vector of a row of (13). -/
def row13Coeff {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (g₀ : G) : Row13 G g₀ → MasterIndex G → ℝ
  | .target => coord g₀
  | .complement g _ => coord (g : G) + coord (g₀ - g)
  | .subadd g h => coord (g : G) + coord (h : G) - coord ((g : G) + h)
  | .nonnegative g => coord (g : G)

/-- Right-hand side of a row of (13). -/
def row13Rhs {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (g₀ : G) (π₀ : ℝ) : Row13 G g₀ → ℝ
  | .target => π₀
  | .complement _ _ => π₀
  | .subadd _ _ => 0
  | .nonnegative _ => 0

/-- The first two families in (13) are equations. -/
def row13Equation {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (g₀ : G) : Set (Row13 G g₀) :=
  {r | match r with
    | .target => True
    | .complement _ _ => True
    | .subadd _ _ => False
    | .nonnegative _ => False}

/-- Feasibility for the finite subadditive system (13), with fixed `π₀`. -/
def System13Feasible {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (g₀ : G) (π₀ : ℝ) (π : MasterIndex G → ℝ) : Prop :=
  ∀ r : Row13 G g₀,
    (r ∈ row13Equation g₀ → rowEval (row13Coeff g₀ r) π = row13Rhs g₀ π₀ r) ∧
    (r ∉ row13Equation g₀ → row13Rhs g₀ π₀ r ≤ rowEval (row13Coeff g₀ r) π)

/-- A basic feasible solution of (13), with its `D - 1` coefficient variables. -/
def IsSystem13Basic {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (g₀ : G) (π₀ : ℝ) (π : MasterIndex G → ℝ) : Prop :=
  IsBasicFeasible (row13Coeff g₀) (row13Rhs g₀ π₀) (row13Equation g₀) π

end Gomory69.MasterFaces
