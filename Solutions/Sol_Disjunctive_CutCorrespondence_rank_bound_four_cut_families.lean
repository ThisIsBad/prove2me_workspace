import Mathlib
import Definitions.Def_Disjunctive_CutCorrespondence_Basic
import Definitions.Def_Disjunctive_CutCorrespondence_Cglp
import Definitions.Def_Disjunctive_CutCorrespondence_Tableau
import Definitions.Def_Disjunctive_CutCorrespondence_Rank

namespace Disjunctive.CutCorrespondence

namespace CexGoal

noncomputable def A : Matrix (Fin 4) (Fin 2) ℝ := !![1, -1; 0, 1; 1, 0; -1, 0]
noncomputable def b : Fin 4 → ℝ := ![1 / 2, 0, 0, -1]
def ι : Fin 2 → Fin 4 := ![0, 1]

lemma ahat : Ahat A ι = !![1, -1; 0, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Ahat, A, ι]

lemma ahat_inv : (Ahat A ι)⁻¹ = !![1, 1; 0, 1] := by
  rw [ahat]
  apply Matrix.inv_eq_left_inv
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

lemma ahat_det : IsUnit (Ahat A ι).det := by
  rw [ahat, Matrix.det_fin_two_of]; norm_num

lemma abar0 : Abar0 A b ι 0 = 1 / 2 := by
  rw [Abar0, ahat_inv]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Bhat, b, ι]

lemma hbounds : Poly A b ⊆ {x | ∀ j ∈ ({0} : Finset (Fin 2)), 0 ≤ x j ∧ x j ≤ 1} := by
  intro x hx
  simp only [Poly, Set.mem_setOf_eq] at hx
  have h2 := hx 2
  have h3 := hx 3
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, A, b] at h2 h3
  simp only [Set.mem_setOf_eq, Finset.mem_singleton, forall_eq]
  constructor <;> linarith

noncomputable def xs : Fin 2 → ℝ := ![1, 0]

lemma xs_mem : xs ∈ Poly A b := by
  intro i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, A, b, xs] <;> norm_num

lemma fract_neg_one : Int.fract (-1 : ℝ) = 0 := by
  rw [show (-1 : ℝ) = ((-1 : ℤ) : ℝ) by norm_num, Int.fract_intCast]

lemma xs_not : xs ∉ StrengthenedSimpleDisjCutSet A b ι 0 {0} := by
  simp only [StrengthenedSimpleDisjCutSet, Set.mem_setOf_eq, Fin.sum_univ_two, PiBar,
    Pi0, abar0, FracAbar, Abar, ahat_inv, PiCoef, Pi1, Pi2, Surplus]
  simp [ι, A, b, xs, dotProduct, Fin.sum_univ_two, fract_neg_one]
  norm_num

theorem cex_goal : ¬ (∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (Nprime : Finset (Fin n))
    (hbounds : Poly A b ⊆ {x | ∀ j ∈ Nprime, 0 ≤ x j ∧ x j ≤ 1}),
    HasRankAtMost SplitConvexify (Poly A b) Nprime Nprime.card ∧
      HasRankAtMost SimpleDisjClosureOfSet (Poly A b) Nprime Nprime.card ∧
      HasRankAtMost (fun S k => StrengthenedLPClosureOfSet S k Nprime) (Poly A b) Nprime
        Nprime.card ∧
      HasRankAtMost (fun S k => MIGClosureOfSet S k Nprime) (Poly A b) Nprime Nprime.card) := by
  intro h
  obtain ⟨-, -, -, hd⟩ := h A b {0} hbounds
  obtain ⟨l, -, hset, hlen, heq⟩ := hd
  rw [Finset.card_singleton, List.length_eq_one_iff] at hlen
  obtain ⟨j, rfl⟩ := hlen
  simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
    Finset.singleton_inj] at hset
  subst hset
  simp only [IterateCutStep, List.foldl] at heq
  have hx : xs ∈ convexHull ℝ (Poly A b ∩ ⋂ j ∈ ({0} : Finset (Fin 2)), ZeroOneSet j) := by
    apply subset_convexHull
    refine ⟨xs_mem, ?_⟩
    simp [ZeroOneSet, xs]
  rw [← heq] at hx
  simp only [MIGClosureOfSet, Set.mem_iInter] at hx
  have h1 := (hx 4 A b rfl).2
  simp only [Set.mem_iInter] at h1
  exact xs_not (h1 ι (by decide) ahat_det (by rw [abar0]; norm_num) (by rw [abar0]; norm_num))

end CexGoal

end Disjunctive.CutCorrespondence

open Disjunctive.CutCorrespondence

theorem solution : ¬ (∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (Nprime : Finset (Fin n))
    (hbounds : Poly A b ⊆ {x | ∀ j ∈ Nprime, 0 ≤ x j ∧ x j ≤ 1}),
    HasRankAtMost SplitConvexify (Poly A b) Nprime Nprime.card ∧
      HasRankAtMost SimpleDisjClosureOfSet (Poly A b) Nprime Nprime.card ∧
      HasRankAtMost (fun S k => StrengthenedLPClosureOfSet S k Nprime) (Poly A b) Nprime
        Nprime.card ∧
      HasRankAtMost (fun S k => MIGClosureOfSet S k Nprime) (Poly A b) Nprime Nprime.card) := by
  exact Disjunctive.CutCorrespondence.CexGoal.cex_goal
