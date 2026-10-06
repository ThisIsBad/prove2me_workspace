import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_SBFR
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_TRFR
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_LinearWeightR
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_ArgMinR

open Classical
open scoped Pointwise

open DiscreteConvex.ConjugacyDualityB

theorem solution : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V]
    (g : (V → ℝ) → WithTop ℝ) (hg : SBFR g ∧ TRFR g)
    (x y : V → ℝ) (hx : (ArgMinR (LinearWeightR g x)).Nonempty)
    (hy : (ArgMinR (LinearWeightR g y)).Nonempty)
    (u : V) (hu : y u < x u),
    ∃ v : V, x v < y v ∧ ∀ p ∈ ArgMinR (LinearWeightR g x),
      ∀ q ∈ ArgMinR (LinearWeightR g y), p v - p u ≤ q v - q u) := by
  intro H
  have hall : ∀ z : Unit → ℝ, ArgMinR (LinearWeightR (fun _ : Unit → ℝ => (⊤ : WithTop ℝ)) z)
      = Set.univ := by
    intro z
    ext p
    simp [ArgMinR, LinearWeightR]
  have hg : SBFR (fun _ : Unit → ℝ => (⊤ : WithTop ℝ)) ∧ TRFR (fun _ : Unit → ℝ => (⊤ : WithTop ℝ)) := by
    refine ⟨fun p q => by simp, ⟨0, fun p a => by simp⟩⟩
  obtain ⟨v, hv, -⟩ := H (fun _ : Unit → ℝ => (⊤ : WithTop ℝ)) hg (fun _ => 1) (fun _ => 0)
    (by rw [hall]; exact Set.univ_nonempty) (by rw [hall]; exact Set.univ_nonempty) () (by norm_num)
  norm_num at hv
