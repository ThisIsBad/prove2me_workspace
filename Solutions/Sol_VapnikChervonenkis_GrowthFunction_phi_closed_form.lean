import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_Phi

namespace VapnikChervonenkis.GrowthFunction

theorem aux_phicf_sum (n r : ℕ) :
    Shared.Phi n r = ∑ k ∈ Finset.range (n + 1), r.choose k := by
  induction n generalizing r with
  | zero => simp [Shared.Phi]
  | succ n ih =>
    induction r with
    | zero =>
      rw [Shared.Phi, Finset.sum_range_succ']
      simp
    | succ r ihr =>
      rw [Shared.Phi, ihr, ih r]
      rw [Finset.sum_range_succ' (fun k => (r + 1).choose k), Finset.sum_range_succ' (fun k => r.choose k)]
      simp only [Nat.choose_succ_succ, Finset.sum_add_distrib, Nat.choose_zero_right]
      ring

theorem aux_phicf_pow (n r : ℕ) (h : r ≤ n) :
    ∑ k ∈ Finset.range (n + 1), r.choose k = 2 ^ r := by
  induction n, h using Nat.le_induction with
  | base => exact Nat.sum_range_choose r
  | succ n hn ih =>
    rw [Finset.sum_range_succ, ih, Nat.choose_eq_zero_of_lt (by omega), add_zero]

end VapnikChervonenkis.GrowthFunction

open VapnikChervonenkis VapnikChervonenkis.GrowthFunction

theorem solution (n r : ℕ) :
    Shared.Phi n r = if n < r then ∑ k ∈ Finset.range (n + 1), r.choose k else 2 ^ r := by
  rw [aux_phicf_sum]
  split_ifs with h
  · rfl
  · exact aux_phicf_pow n r (by omega)
