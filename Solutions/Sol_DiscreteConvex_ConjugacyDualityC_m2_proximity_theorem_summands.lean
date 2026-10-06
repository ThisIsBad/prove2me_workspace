import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_IndicatorVec
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_DomZ
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_ArgMin
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_MExchangeAxiom

set_option autoImplicit false
set_option linter.unusedVariables false

open DiscreteConvex.ConjugacyDualityC

namespace M2Cex

/-- `y ↦ c * y 0` on the hyperplane `y 0 + y 1 = 0`. -/
noncomputable def F (c : ℝ) (y : Fin 2 → ℤ) : WithTop ℝ :=
  if y 0 + y 1 = 0 then ((c * (y 0 : ℝ) : ℝ) : WithTop ℝ) else ⊤

theorem F_of (c : ℝ) (y : Fin 2 → ℤ) (h : y 0 + y 1 = 0) : F c y = ((c * (y 0 : ℝ) : ℝ) : WithTop ℝ) := by
  simp [F, h]

theorem F_dom (c : ℝ) (y : Fin 2 → ℤ) (h : y ∈ DomZ (F c)) : y 0 + y 1 = 0 := by
  by_contra hc
  simp [DomZ, F, hc] at h

theorem F_exc (c : ℝ) : MExchangeAxiom (F c) := by
  intro x hx y hy u hu
  have hx' := F_dom c x hx
  have hy' := F_dom c y hy
  simp only [SuppPos, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  fin_cases u
  · refine ⟨1, ?_, ?_⟩
    · simp only [SuppNeg, Finset.mem_filter, Finset.mem_univ, true_and]
      simp at hu; omega
    · rw [F_of c x hx', F_of c y hy', F_of, F_of]
      · apply le_of_eq; rw [← WithTop.coe_add, ← WithTop.coe_add]; congr 1
        simp [IndicatorVec]; ring
      · simp [IndicatorVec]; omega
      · simp [IndicatorVec]; omega
  · refine ⟨0, ?_, ?_⟩
    · simp only [SuppNeg, Finset.mem_filter, Finset.mem_univ, true_and]
      simp at hu; omega
    · rw [F_of c x hx', F_of c y hy', F_of, F_of]
      · apply le_of_eq; rw [← WithTop.coe_add, ← WithTop.coe_add]; congr 1
        simp [IndicatorVec]; ring
      · simp [IndicatorVec]; omega
      · simp [IndicatorVec]; omega


theorem P1 (a b : Fin 2) :
    F 1 (fun w => (0 : Fin 2 → ℤ) w - (1 : ℤ) * (IndicatorVec {a} w - IndicatorVec {b} w)) - F 1 0
      = ((-((IndicatorVec {a} 0 : ℝ) - IndicatorVec {b} 0) : ℝ) : WithTop ℝ) := by
  rw [F_of _ _ (by fin_cases a <;> fin_cases b <;> simp [IndicatorVec]), F_of _ _ (by simp),
    ← WithTop.LinearOrderedAddCommGroup.coe_sub]
  congr 1
  push_cast; ring

theorem P2 (a b : Fin 2) :
    F 1 (fun w => (0 : Fin 2 → ℤ) w + (1 : ℤ) * (IndicatorVec {a} w - IndicatorVec {b} w)) - F 1 0
      = ((((IndicatorVec {a} 0 : ℝ) - IndicatorVec {b} 0) : ℝ) : WithTop ℝ) := by
  rw [F_of _ _ (by fin_cases a <;> fin_cases b <;> simp [IndicatorVec]), F_of _ _ (by simp),
    ← WithTop.LinearOrderedAddCommGroup.coe_sub]
  congr 1
  push_cast; ring

theorem argmin_empty : ¬ (ArgMin (fun x => F 1 x + F 1 x)).Nonempty := by
  rintro ⟨x, hx⟩
  by_cases h : x 0 + x 1 = 0
  · have := hx ![x 0 - 1, 1 - x 0]
    dsimp only at this
    rw [F_of _ _ h, F_of _ _ (by simp), ← WithTop.coe_add, ← WithTop.coe_add,
      WithTop.coe_le_coe] at this
    simp at this
    linarith
  · have := hx 0
    dsimp only at this
    rw [F_of 1 0 (by simp)] at this
    simp [F, h] at this

end M2Cex


theorem solution : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V]
    (f1 f2 : (V → ℤ) → WithTop ℝ) (hf1 : MExchangeAxiom f1)
    (hf2 : MExchangeAxiom f2) (alpha : ℤ) (halpha : 0 < alpha) (xalpha : V → ℤ)
    (hxalpha : xalpha ∈ DomZ f1 ∩ DomZ f2)
    (hcond : ∀ k : ℕ, ∀ u v : Fin (k + 1) → V, (∀ i j, u i ≠ v j) →
      (∑ i : Fin (k + 1),
          (f1 (fun w => xalpha w - alpha * (IndicatorVec {u i} w - IndicatorVec {v i} w)) -
            f1 xalpha)) +
        (∑ i : Fin (k + 1),
          (f2 (fun w => xalpha w + alpha * (IndicatorVec {u (i + 1)} w - IndicatorVec {v i} w)) -
            f2 xalpha)) ≥
        0),
    (ArgMin (fun x => f1 x + f2 x)).Nonempty ∧
      ∃ xstar ∈ ArgMin (fun x => f1 x + f2 x), ∀ w : V,
        |(xalpha w : ℝ) - (xstar w : ℝ)| ≤ (((Fintype.card V : ℝ) ^ 2) / 2) * ((alpha : ℝ) - 1)) := by
  intro h
  have h0 : (0 : Fin 2 → ℤ) ∈ DomZ (M2Cex.F 1) ∩ DomZ (M2Cex.F 1) := by
    constructor <;> simp [DomZ, M2Cex.F]
  refine M2Cex.argmin_empty (h (M2Cex.F 1) (M2Cex.F 1) (M2Cex.F_exc 1) (M2Cex.F_exc 1) 1 one_pos 0
    h0 ?_).1
  intro k u v _
  simp only [M2Cex.P1, M2Cex.P2]
  rw [← WithTop.coe_sum, ← WithTop.coe_sum, ← WithTop.coe_add, ge_iff_le, ← WithTop.coe_zero,
    WithTop.coe_le_coe]
  have hs : ∑ i : Fin (k + 1), (IndicatorVec {u (i + 1)} 0 : ℝ) =
      ∑ i : Fin (k + 1), (IndicatorVec {u i} 0 : ℝ) :=
    Equiv.sum_comp (Equiv.addRight (1 : Fin (k + 1))) (fun i => (IndicatorVec {u i} 0 : ℝ))
  simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib, hs]
  linarith
