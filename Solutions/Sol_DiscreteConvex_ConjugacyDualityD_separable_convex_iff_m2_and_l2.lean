import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_MNaturalConvex
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_LNaturalConvex
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_MNat2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_LNat2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_IsSeparableConvex

set_option autoImplicit false

open DiscreteConvex.ConjugacyDualityD

namespace SepCex

def fTop : (Unit → ℤ) → WithTop ℝ := fun _ => ⊤

theorem mnat : MNaturalConvex fTop := by
  intro x hx
  exfalso; apply hx
  simp [LiftedFunction, fTop]

theorem lnat : LNaturalConvex fTop :=
  ⟨fun _ _ => le_top, ⟨0, fun _ => by simp [LiftedFunctionL, fTop]⟩⟩

theorem not_sep : ¬ IsSeparableConvex fTop := by
  rintro ⟨psi, hpsi, hf⟩
  obtain ⟨x, hx⟩ := (hpsi ()).1
  have := hf (fun _ => x)
  simp only [Finset.univ_unique, Finset.sum_singleton, fTop] at this
  exact hx this.symm

end SepCex

theorem solution : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ),
    [MNat2Convex f ∧ LNat2Convex f, MNaturalConvex f ∧ LNaturalConvex f,
        IsSeparableConvex f].TFAE) := by
  intro h
  have H := (h SepCex.fTop).out 1 2
  exact SepCex.not_sep (H.mp (And.intro SepCex.mnat SepCex.lnat))

#print axioms solution
