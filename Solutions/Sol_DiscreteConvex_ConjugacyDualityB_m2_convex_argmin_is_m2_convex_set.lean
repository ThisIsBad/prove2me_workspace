import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_ArgMin
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_M2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_MNat2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_M2ConvexSet
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_MNat2ConvexSet

open Classical
open scoped Pointwise

open DiscreteConvex.ConjugacyDualityB

theorem solution : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V],
    (∀ f : (V → ℤ) → WithTop ℝ, M2Convex f → (ArgMin f).Nonempty → M2ConvexSet (ArgMin f)) ∧
    (∀ f : (V → ℤ) → WithTop ℝ, MNat2Convex f → (ArgMin f).Nonempty → MNat2ConvexSet (ArgMin f))) := by
  intro H
  have hT : MExchangeAxiom (fun _ : Unit → ℤ => (⊤ : WithTop ℝ)) := by
    intro x hx
    simp [DomZ] at hx
  have hM : M2Convex (fun x : Unit → ℤ => (fun _ : Unit → ℤ => (⊤ : WithTop ℝ)) x +
      (fun _ : Unit → ℤ => (⊤ : WithTop ℝ)) x) := ⟨_, _, hT, hT, rfl⟩
  have hA : ArgMin (fun x : Unit → ℤ => (fun _ : Unit → ℤ => (⊤ : WithTop ℝ)) x +
      (fun _ : Unit → ℤ => (⊤ : WithTop ℝ)) x) = Set.univ := by
    ext x; simp [ArgMin]
  obtain ⟨D1, D2, h1, h2, hD⟩ := (H (V := Unit)).1 _ hM (by rw [hA]; exact Set.univ_nonempty)
  rw [hA] at hD
  have hx : (fun _ : Unit => (1 : ℤ)) ∈ D1 := by
    have := Set.mem_univ (fun _ : Unit => (1 : ℤ)); rw [hD] at this; exact this.1
  have hy : (fun _ : Unit => (0 : ℤ)) ∈ D1 := by
    have := Set.mem_univ (fun _ : Unit => (0 : ℤ)); rw [hD] at this; exact this.1
  obtain ⟨v, hv, -⟩ := h1 _ hx _ hy () (by simp [SuppPos])
  simp [SuppNeg] at hv
