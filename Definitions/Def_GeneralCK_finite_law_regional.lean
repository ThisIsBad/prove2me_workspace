import Definitions.Def_GeneralCK_bellman
import Definitions.Def_GeneralCK_statement
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace GeneralCK
open scoped BigOperators

structure InteriorLaw (ι : Type*) [Fintype ι] where
  weight : ι → ℝ
  left : ι → ℝ
  right : ι → ℝ
  weight_nonneg : ∀ i, 0 ≤ weight i
  weight_sum : ∑ i, weight i = 1
  left_interior : ∀ i, 0 < left i ∧ left i < 1
  right_interior : ∀ i, 0 < right i ∧ right i < 1

namespace InteriorLaw
variable {ι : Type*} [Fintype ι]

noncomputable def avg (μ : InteriorLaw ι) (v : ι → ℝ) : ℝ := ∑ i, μ.weight i * v i
noncomputable def a (μ : InteriorLaw ι) : ℝ := μ.avg μ.left
noncomputable def b (μ : InteriorLaw ι) : ℝ := μ.avg μ.right
noncomputable def e (μ : InteriorLaw ι) : ℝ := μ.avg (H ∘ μ.left)
noncomputable def f (μ : InteriorLaw ι) : ℝ := μ.avg (H ∘ μ.right)
noncomputable def cost (μ : InteriorLaw ι) : ℝ :=
  μ.avg (fun i => interiorCost (μ.left i) (μ.right i))
noncomputable def gap (μ : InteriorLaw ι) : ℝ :=
  B ((μ.a + μ.b) / 2) ((μ.e + μ.f) / 2) - (B μ.a μ.e + B μ.b μ.f) / 2
























def swap (μ : InteriorLaw ι) : InteriorLaw ι where
  weight := μ.weight
  left := μ.right
  right := μ.left
  weight_nonneg := μ.weight_nonneg
  weight_sum := μ.weight_sum
  left_interior := μ.right_interior
  right_interior := μ.left_interior

def complement (μ : InteriorLaw ι) : InteriorLaw ι where
  weight := μ.weight
  left := fun i => 1 - μ.left i
  right := fun i => 1 - μ.right i
  weight_nonneg := μ.weight_nonneg
  weight_sum := μ.weight_sum
  left_interior := fun i => by have := μ.left_interior i; constructor <;> linarith
  right_interior := fun i => by have := μ.right_interior i; constructor <;> linarith










end InteriorLaw







namespace InteriorLaw
variable {ι : Type*} [Fintype ι]








end InteriorLaw



end GeneralCK

namespace GeneralCK.ArchiveRegionalBoundary

structure Inputs : Prop where
  sameSide : ∀ (k : ℕ) (μ : GeneralCK.InteriorLaw (Fin k)),
    μ.a ≤ μ.b → μ.a + μ.b ≤ 1 → μ.b ≤ 1 / 2 → μ.gap ≤ μ.cost
  oppositeSide : ∀ (k : ℕ) (μ : GeneralCK.InteriorLaw (Fin k)),
    μ.a ≤ μ.b → μ.a + μ.b ≤ 1 → 1 / 2 ≤ μ.b → μ.gap ≤ μ.cost








end GeneralCK.ArchiveRegionalBoundary
