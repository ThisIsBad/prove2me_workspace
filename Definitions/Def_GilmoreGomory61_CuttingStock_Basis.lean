import Mathlib
import Definitions.Def_GilmoreGomory61_CuttingStock_Model

namespace GilmoreGomory61.CuttingStock

/-- Matrix A of the current m basic columns, p. 852. -/
def basisMat {m k : ℕ} (I : Instance m k) (β : Fin m → Col I) :
    Matrix (Fin m) (Fin m) ℝ := Matrix.of fun i r => colVec I (β r) i

/-- The cost row C of the basic columns. -/
def costRow {m k : ℕ} (I : Instance m k) (β : Fin m → Col I) : Fin m → ℝ :=
  fun r => colCost I (β r)

/-- The bordered matrix B of routine step (2), after any basis change. -/
def bordered {m k : ℕ} (I : Instance m k) (β : Fin m → Col I) :
    Matrix (Unit ⊕ Fin m) (Unit ⊕ Fin m) ℝ :=
  Matrix.fromBlocks 1 (Matrix.of fun _ r => -costRow I β r) 0 (basisMat I β)

/-- The bordered demand vector N′, with zero cost coordinate. -/
def Nprime {m k : ℕ} (I : Instance m k) : Unit ⊕ Fin m → ℝ :=
  Sum.elim (fun _ => 0) (fun i => (I.N i : ℝ))

/-- The current tableau right-hand column B⁻¹N′. -/
noncomputable def Nbar {m k : ℕ} (I : Instance m k) (β : Fin m → Col I) :
    Unit ⊕ Fin m → ℝ := Matrix.mulVec (bordered I β)⁻¹ (Nprime I)

/-- The last m entries of the first row of B⁻¹, routine step (4). -/
noncomputable def mult {m k : ℕ} (I : Instance m k) (β : Fin m → Col I) : Fin m → ℝ :=
  fun i => (bordered I β)⁻¹ (Sum.inl ()) (Sum.inr i)

/-- The bordered column P for either an activity or a surplus variable. -/
def extCol {m k : ℕ} (I : Instance m k) (j : Col I) : Unit ⊕ Fin m → ℝ :=
  Sum.elim (fun _ => -colCost I j) (colVec I j)

/-- The first entry of B⁻¹P, the paper's pricing quantity. -/
noncomputable def priceOut {m k : ℕ} (I : Instance m k) (β : Fin m → Col I)
    (j : Col I) : ℝ := (Matrix.mulVec (bordered I β)⁻¹ (extCol I j)) (Sum.inl ())

/-- The current basic solution, using only columns in β. -/
noncomputable def basicSol {m k : ℕ} (I : Instance m k) (β : Fin m → Col I) :
    Col I →₀ ℝ :=
  ∑ r : Fin m, Finsupp.single (β r) (Nbar I β (Sum.inr r))

/-- Invertible basic columns with nonnegative basic values. -/
def IsFeasibleBasis {m k : ℕ} (I : Instance m k) (β : Fin m → Col I) : Prop :=
  IsUnit (basisMat I β).det ∧ ∀ r, 0 ≤ Nbar I β (Sum.inr r)

/-- Strict positivity of every current basic value. -/
def IsNondegenerate {m k : ℕ} (I : Instance m k) (β : Fin m → Col I) : Prop :=
  ∀ r, 0 < Nbar I β (Sum.inr r)

/-- A strictly cheaper feasible solution using only the current basis and one candidate column. -/
def Improves {m k : ℕ} (I : Instance m k) (β : Fin m → Col I) (j : Col I) : Prop :=
  ∃ z : Col I →₀ ℝ, Feasible I z ∧
    (∀ j' ∈ z.support, j' ∈ Set.range β ∨ j' = j) ∧
    cost I z < cost I (basicSol I β)

end GilmoreGomory61.CuttingStock
