import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_MExchangeAxiomR
import Definitions.Def_DiscreteConvex_NetworkFlowsB_HasNegativeCycle
import Definitions.Def_DiscreteConvex_NetworkFlowsB_FeasibleFlowMSFP2
import Definitions.Def_DiscreteConvex_NetworkFlowsB_OptimalFlowMSFP2
import Definitions.Def_DiscreteConvex_NetworkFlowsB_AuxTailMSFP2
import Definitions.Def_DiscreteConvex_NetworkFlowsB_AuxHeadMSFP2
import Definitions.Def_DiscreteConvex_NetworkFlowsB_AuxActiveMSFP2
import Definitions.Def_DiscreteConvex_NetworkFlowsB_AuxLengthMSFP2

open Classical
open scoped Pointwise

namespace DiscreteConvex.NetworkFlowsB

namespace MSFP2Cex

noncomputable def fC (y : Bool → ℝ) : WithTop ℝ :=
  if y true + y false = 0 ∧ 0 ≤ y true then ((-Real.sqrt (y true) : ℝ) : WithTop ℝ) else ⊤

def tl : Unit → Bool := fun _ => true
def hd : Unit → Bool := fun _ => false

lemma sqrt_exch (a b α : ℝ) (hb : 0 ≤ b) (hα : 0 ≤ α) (hab : b + α ≤ a - α) :
    Real.sqrt a + Real.sqrt b ≤ Real.sqrt (a - α) + Real.sqrt (b + α) := by
  have ha : 0 ≤ a := by linarith
  have h1 : Real.sqrt a * Real.sqrt b ≤ Real.sqrt (a - α) * Real.sqrt (b + α) := by
    rw [← Real.sqrt_mul ha, ← Real.sqrt_mul (by linarith)]
    apply Real.sqrt_le_sqrt
    nlinarith
  have hp := Real.sq_sqrt ha
  have hq := Real.sq_sqrt hb
  have hr := Real.sq_sqrt (show 0 ≤ a - α by linarith)
  have hs := Real.sq_sqrt (show 0 ≤ b + α by linarith)
  have hsq : (Real.sqrt a + Real.sqrt b) ^ 2 ≤ (Real.sqrt (a - α) + Real.sqrt (b + α)) ^ 2 := by
    nlinarith
  have := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq (by positivity)] at this

lemma fC_mexc : MExchangeAxiomR fC := by
  intro x hx y hy u hu
  simp only [DomR, Set.mem_setOf_eq, fC, ne_eq, ite_eq_right_iff, not_forall] at hx hy
  obtain ⟨⟨hx1, hx2⟩, -⟩ := hx
  obtain ⟨⟨hy1, hy2⟩, -⟩ := hy
  simp only [SuppPosR, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  cases u with
  | true =>
    refine ⟨false, by simp only [SuppNegR, Finset.mem_filter, Finset.mem_univ, true_and]; linarith,
      (x true - y true) / 2, by linarith, fun α hα0 hα1 => ?_⟩
    simp only [fC]
    rw [if_pos ⟨hx1, hx2⟩, if_pos ⟨hy1, hy2⟩]
    simp only [if_true, if_false, Bool.true_eq_false, Bool.false_eq_true, mul_one, mul_zero,
      sub_zero, add_zero, zero_add]
    rw [if_pos ⟨by linarith, by linarith⟩, if_pos ⟨by linarith, by linarith⟩]
    have := sqrt_exch (x true) (y true) α hy2 hα0 (by linarith)
    rw [ge_iff_le]
    exact_mod_cast (show -Real.sqrt (x true - α) + -Real.sqrt (y true + α) ≤
      -Real.sqrt (x true) + -Real.sqrt (y true) by linarith)
  | false =>
    refine ⟨true, by simp only [SuppNegR, Finset.mem_filter, Finset.mem_univ, true_and]; linarith,
      (y true - x true) / 2, by linarith, fun α hα0 hα1 => ?_⟩
    simp only [fC]
    rw [if_pos ⟨hx1, hx2⟩, if_pos ⟨hy1, hy2⟩]
    simp only [if_true, if_false, Bool.true_eq_false, Bool.false_eq_true, mul_one, mul_zero,
      sub_zero, add_zero, zero_add]
    rw [if_pos ⟨by linarith, by linarith⟩, if_pos ⟨by linarith, by linarith⟩]
    have := sqrt_exch (y true) (x true) α hx2 hα0 (by linarith)
    rw [ge_iff_le]
    exact_mod_cast (show -Real.sqrt (x true + α) + -Real.sqrt (y true - α) ≤
      -Real.sqrt (x true) + -Real.sqrt (y true) by linarith)

lemma bnd (c : ℝ) : Boundary tl hd (fun _ : Unit => c) = fun w => if w = true then c else -c := by
  funext w
  cases w <;> simp [Boundary, tl, hd]

lemma elem (t : ℝ) (ht : 0 < t) :
    PosScalarMul (1 / t) (fC (fun w => Boundary tl hd (fun _ : Unit => (0:ℝ)) w +
      t * (-(if w = false then (1:ℝ) else 0) + if w = true then 1 else 0)) -
      fC (Boundary tl hd (fun _ : Unit => (0:ℝ)))) = ((-Real.sqrt t / t : ℝ) : WithTop ℝ) := by
  rw [bnd 0]
  have e1 : fC (fun w => (fun w => if w = true then (0:ℝ) else -0) w +
      t * (-(if w = false then (1:ℝ) else 0) + if w = true then 1 else 0)) =
      ((-Real.sqrt t : ℝ) : WithTop ℝ) := by
    unfold fC
    rw [if_pos (by simp; linarith)]
    simp
  have e2 : fC (fun w => if w = true then (0:ℝ) else -0) = ((0:ℝ) : WithTop ℝ) := by
    unfold fC; simp
  rw [e1, e2]
  have e3 : ((-Real.sqrt t : ℝ) : WithTop ℝ) - ((0:ℝ) : WithTop ℝ) = ((-Real.sqrt t - 0 : ℝ) : WithTop ℝ) := rfl
  rw [e3]
  show (((1 / t) * (-Real.sqrt t - 0) : ℝ) : WithTop ℝ) = _
  congr 1
  ring

theorem msfp2_cex : ¬ (∀ {V A : Type} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
    (tail head : A → V) (cUpper : A → WithTop ℝ)
    (cLower : A → WithBot ℝ) (gamma : A → ℝ) (f : (V → ℝ) → WithTop ℝ) (hf : MExchangeAxiomR f)
    (xi : A → ℝ) (hfeas : FeasibleFlowMSFP2 tail head cUpper cLower f xi),
    OptimalFlowMSFP2 tail head cUpper cLower gamma f xi ↔
      ¬ HasNegativeCycle (AuxTailMSFP2 tail head) (AuxHeadMSFP2 tail head)
        (AuxActiveMSFP2 tail head cUpper cLower f xi) (AuxLengthMSFP2 tail head gamma f xi)) := by
  intro H
  have hb0 := bnd 0
  have hb1 := bnd 1
  have hf0 : fC (Boundary tl hd (fun _ : Unit => (0:ℝ))) = ((0:ℝ) : WithTop ℝ) := by
    rw [hb0]; simp [fC]
  have hf1 : fC (Boundary tl hd (fun _ : Unit => (1:ℝ))) = ((-1:ℝ) : WithTop ℝ) := by
    rw [hb1]; simp [fC]
  have hfeas : FeasibleFlowMSFP2 tl hd (fun _ => ⊤) (fun _ => ⊥) fC (fun _ => 0) :=
    ⟨fun _ => ⟨bot_le, le_top⟩, by rw [hf0]; exact WithTop.coe_ne_top⟩
  have hfeas1 : FeasibleFlowMSFP2 tl hd (fun _ => ⊤) (fun _ => ⊥) fC (fun _ => 1) :=
    ⟨fun _ => ⟨bot_le, le_top⟩, by rw [hf1]; exact WithTop.coe_ne_top⟩
  have key := H tl hd (fun _ => ⊤) (fun _ => ⊥) (fun _ => 0) fC fC_mexc (fun _ => 0) hfeas
  have hnot : ¬ OptimalFlowMSFP2 tl hd (fun _ => ⊤) (fun _ => ⊥) (fun _ => 0) fC (fun _ => 0) := by
    intro ho
    have := ho.2 _ hfeas1
    unfold Gamma2 at this
    rw [hf0, hf1] at this
    simp only [mul_zero, Finset.sum_const_zero] at this
    norm_cast at this
  apply hnot
  rw [key]
  rintro ⟨k, c, hact, -, hneg⟩
  have hnn : ∀ i, (0 : WithTop ℝ) ≤ AuxLengthMSFP2 tl hd (fun _ => 0) fC (fun _ => 0) (c i) := by
    intro i
    have hai := hact i
    rcases hci : c i with a | a | ⟨u, v⟩
    · simp [AuxLengthMSFP2]
    · simp [AuxLengthMSFP2]
    · rw [hci] at hai
      obtain ⟨huv, α, hα, hfin⟩ := hai
      cases u <;> cases v
      · exact absurd rfl huv
      · -- u = false, v = true : length is ⊤
        simp only [AuxLengthMSFP2]
        rw [DirDeriv, WithTop.sInf_of_not_bddBelow]
        · exact le_top
        rintro ⟨b, hb⟩
        induction b using WithTop.recTopCoe with
        | top =>
          have hm := hb ⟨1, one_pos, (elem 1 one_pos).symm⟩
          exact absurd hm (by simp)
        | coe M =>
          set s : ℝ := 1 / (|M| + 1) with hs
          have hs0 : 0 < s := by positivity
          have hm := hb ⟨s ^ 2, by positivity, (elem (s ^ 2) (by positivity)).symm⟩
          rw [WithTop.coe_le_coe, Real.sqrt_sq hs0.le] at hm
          have : -s / s ^ 2 = -(|M| + 1) := by
            rw [hs]; field_simp
          rw [this] at hm
          linarith [le_abs_self M, neg_abs_le M]
      · -- u = true, v = false : not active
        exfalso
        apply hfin
        rw [hb0]
        simp only [fC]
        rw [if_neg]
        rintro ⟨-, h⟩
        simp at h
        linarith
      · exact absurd rfl huv
  have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hnn i)
  exact absurd hneg (not_lt.2 this)

end MSFP2Cex

end DiscreteConvex.NetworkFlowsB

open DiscreteConvex.NetworkFlowsB


theorem solution : ¬ (∀ {V A : Type} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
    (tail head : A → V) (cUpper : A → WithTop ℝ)
    (cLower : A → WithBot ℝ) (gamma : A → ℝ) (f : (V → ℝ) → WithTop ℝ) (hf : MExchangeAxiomR f)
    (xi : A → ℝ) (hfeas : FeasibleFlowMSFP2 tail head cUpper cLower f xi),
    OptimalFlowMSFP2 tail head cUpper cLower gamma f xi ↔
      ¬ HasNegativeCycle (AuxTailMSFP2 tail head) (AuxHeadMSFP2 tail head)
        (AuxActiveMSFP2 tail head cUpper cLower f xi) (AuxLengthMSFP2 tail head gamma f xi)) := DiscreteConvex.NetworkFlowsB.MSFP2Cex.msfp2_cex
