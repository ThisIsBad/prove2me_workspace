import Mathlib
import Definitions.Def_LogRegretOCO_FTAL_IsFTLRun

namespace LogRegretOCO.FTAL

/-- Be-the-leader lemma: the shifted run `x (t+1)` beats every fixed comparator in `P`. -/
theorem aux_btl_sum_le {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n)))
    (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (hx : IsFTLRun P f x) (T : ℕ) :
    ∀ u ∈ P, ∑ t ∈ Finset.Icc 1 T, f t (x (t + 1)) ≤ ∑ t ∈ Finset.Icc 1 T, f t u := by
  induction T with
  | zero =>
    intro u _
    simp
  | succ T ih =>
    intro u hu
    have hmem : x (T + 1 + 1) ∈ P := (hx (T + 1 + 1) (by omega)).1
    have hmin := (hx (T + 1 + 1) (by omega)).2 u hu
    rw [Finset.Ico_add_one_right_eq_Icc] at hmin
    have hIH := ih (x (T + 1 + 1)) hmem
    have e1 : ∑ t ∈ Finset.Icc 1 (T + 1), f t (x (t + 1))
        = ∑ t ∈ Finset.Icc 1 T, f t (x (t + 1)) + f (T + 1) (x (T + 1 + 1)) :=
      Finset.sum_Icc_succ_top (by omega) (fun t => f t (x (t + 1)))
    have e2 : ∑ t ∈ Finset.Icc 1 (T + 1), f t (x (T + 1 + 1))
        = ∑ t ∈ Finset.Icc 1 T, f t (x (T + 1 + 1)) + f (T + 1) (x (T + 1 + 1)) :=
      Finset.sum_Icc_succ_top (by omega) (fun t => f t (x (T + 1 + 1)))
    linarith

end LogRegretOCO.FTAL

open LogRegretOCO.FTAL

theorem solution {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n)))
    (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (hx : IsFTLRun P f x) (T : ℕ) :
    ∀ u ∈ P,
      ∑ t ∈ Finset.Icc 1 T, f t (x t) - ∑ t ∈ Finset.Icc 1 T, f t u
        ≤ ∑ t ∈ Finset.Icc 1 T, f t (x t) - ∑ t ∈ Finset.Icc 1 T, f t (x (t + 1)) := by
  intro u hu
  have h := aux_btl_sum_le P f x hx T u hu
  linarith
