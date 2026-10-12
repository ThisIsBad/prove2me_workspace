import Mathlib
import Definitions.Def_KelsoCrawford_ContinuousCore_Model

namespace KelsoCrawford.OneSided

structure Market (W F : Type) where
  u : W → F → ℝ → ℝ
  y : F → Finset W → ℝ
  σ : W → F → ℝ

def profit {W : Type} [DecidableEq W] (y : Finset W → ℝ)
    (C : Finset W) (s : W → ℝ) : ℝ := y C - ∑ i ∈ C, s i

def IsDemanded {W : Type} [DecidableEq W] (y : Finset W → ℝ)
    (s : W → ℝ) (C : Finset W) : Prop :=
  ∀ C' : Finset W, profit y C' s ≤ profit y C s

def GrossSubstitutesOn {W : Type} [DecidableEq W] (y : Finset W → ℝ)
    (S : Set (W → ℝ)) : Prop :=
  ∀ s ∈ S, ∀ s' ∈ S, s ≤ s' → ∀ C, IsDemanded y s C →
    ∃ C', IsDemanded y s' C' ∧ C.filter (fun i => s' i = s i) ⊆ C'

structure Allocation (W F : Type) where
  assign : W → F
  sal : W → ℝ

def Allocation.hired {W F : Type} [Fintype W] [DecidableEq W] [DecidableEq F]
    (A : Allocation W F) (j : F) : Finset W :=
  Finset.univ.filter (fun i => A.assign i = j)

def Market.IsIR {W F : Type} [Fintype W] [DecidableEq W] [Fintype F]
    [DecidableEq F] (M : Market W F) (A : Allocation W F) : Prop :=
  (∀ i, M.σ i (A.assign i) ≤ A.sal i) ∧
    ∀ j, 0 ≤ profit (M.y j) (A.hired j) A.sal

def Market.CanImprove {W F : Type} [Fintype W] [DecidableEq W]
    [Fintype F] [DecidableEq F] (M : Market W F) (R : W → F → Set ℝ)
    (A : Allocation W F) : Prop :=
  ∃ (j : F) (C : Finset W) (r : W → ℝ),
    (∀ i ∈ C, r i ∈ R i j) ∧
    (∀ i ∈ C, M.u i (A.assign i) (A.sal i) ≤ M.u i j (r i)) ∧
    profit (M.y j) (A.hired j) A.sal ≤ profit (M.y j) C r ∧
    ((∃ i ∈ C, M.u i (A.assign i) (A.sal i) < M.u i j (r i)) ∨
      profit (M.y j) (A.hired j) A.sal < profit (M.y j) C r)

def Market.IsStrictCore {W F : Type} [Fintype W] [DecidableEq W]
    [Fintype F] [DecidableEq F] (M : Market W F) (R : W → F → Set ℝ)
    (A : Allocation W F) : Prop :=
  M.IsIR A ∧ (∀ i, A.sal i ∈ R i (A.assign i)) ∧ ¬ M.CanImprove R A

end KelsoCrawford.OneSided
