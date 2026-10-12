import Mathlib
import Definitions.Def_KelsoCrawford_Process_Model

namespace KelsoCrawford.ContinuousCore

structure Market (W F : Type) where
  u : W → F → ℝ → ℝ
  y : F → Finset W → ℝ
  σ : W → F → ℝ

variable {W F : Type} [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F]

def Market.UtilityRegular (M : Market W F) : Prop :=
  ∀ i j, StrictMono (M.u i j) ∧ Continuous (M.u i j)

def Market.MP (M : Market W F) : Prop :=
  ∀ i j (C : Finset W), i ∉ C →
    0 ≤ M.y j (insert i C) - M.y j C - M.σ i j

def Market.NFL (M : Market W F) : Prop := ∀ j, M.y j ∅ = 0

def Market.ReservationSalaries (M : Market W F) : Prop :=
  ∀ i j k, M.u i j (M.σ i j) = M.u i k (M.σ i k)

def Market.grid (M : Market W F) (δ : ℝ) (i : W) (j : F) : Set ℝ :=
  {r | ∃ k : ℕ, r = M.σ i j + k * δ}

def Market.gridVectors (M : Market W F) (δ : ℝ) (j : F) : Set (W → ℝ) :=
  {s | ∀ i, s i ∈ M.grid δ i j}

structure Allocation (W F : Type) where
  assign : W → F
  sal : W → ℝ

def Allocation.hired (A : Allocation W F) (j : F) : Finset W :=
  Finset.univ.filter (fun i => A.assign i = j)

def Market.IsIR (M : Market W F) (A : Allocation W F) : Prop :=
  (∀ i, M.σ i (A.assign i) ≤ A.sal i) ∧
    ∀ j, 0 ≤ KelsoCrawford.Process.profit (M.y j) (A.hired j) A.sal

def anySalary : W → F → Set ℝ := fun _ _ => Set.univ

def Market.CanImprove (M : Market W F) (R : W → F → Set ℝ)
    (A : Allocation W F) : Prop :=
  ∃ (j : F) (C : Finset W) (r : W → ℝ),
    (∀ i ∈ C, r i ∈ R i j) ∧
    (∀ i ∈ C, M.u i (A.assign i) (A.sal i) ≤ M.u i j (r i)) ∧
    KelsoCrawford.Process.profit (M.y j) (A.hired j) A.sal ≤ KelsoCrawford.Process.profit (M.y j) C r ∧
    ((∃ i ∈ C, M.u i (A.assign i) (A.sal i) < M.u i j (r i)) ∨
      KelsoCrawford.Process.profit (M.y j) (A.hired j) A.sal < KelsoCrawford.Process.profit (M.y j) C r)

def Market.CanStrictlyImprove (M : Market W F) (R : W → F → Set ℝ)
    (A : Allocation W F) : Prop :=
  ∃ (j : F) (C : Finset W) (r : W → ℝ),
    (∀ i ∈ C, r i ∈ R i j) ∧
    (∀ i ∈ C, M.u i (A.assign i) (A.sal i) < M.u i j (r i)) ∧
    KelsoCrawford.Process.profit (M.y j) (A.hired j) A.sal < KelsoCrawford.Process.profit (M.y j) C r

def Market.IsStrictCore (M : Market W F) (R : W → F → Set ℝ)
    (A : Allocation W F) : Prop :=
  M.IsIR A ∧ (∀ i, A.sal i ∈ R i (A.assign i)) ∧ ¬ M.CanImprove R A

def Market.IsCore (M : Market W F) (R : W → F → Set ℝ)
    (A : Allocation W F) : Prop :=
  M.IsIR A ∧ (∀ i, A.sal i ∈ R i (A.assign i)) ∧ ¬ M.CanStrictlyImprove R A

end KelsoCrawford.ContinuousCore
