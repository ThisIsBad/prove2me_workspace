import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace CandesTao.LowerBound

end CandesTao.LowerBound

open CandesTao.LowerBound

theorem solution (n : ℕ) (π δ : ℝ)
    (hn : 1 ≤ n) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1) (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (h : (1 - π) ^ n ≥ 1 - δ) :
    π ≤ 2 * δ / n := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hbern : 1 + (n : ℝ) * π ≤ (1 + π) ^ n :=
    one_add_mul_le_pow (by linarith) n
  have hprod : (1 - π) ^ n * (1 + π) ^ n ≤ 1 := by
    rw [← mul_pow]
    apply pow_le_one₀
    · nlinarith
    · nlinarith
  have hpos : 0 ≤ (1 - π) ^ n := pow_nonneg (by linarith) n
  have h1 : (1 - δ) * (1 + (n : ℝ) * π) ≤ 1 := by
    calc (1 - δ) * (1 + (n : ℝ) * π) ≤ (1 - π) ^ n * (1 + (n : ℝ) * π) := by
          apply mul_le_mul_of_nonneg_right h
          positivity
      _ ≤ (1 - π) ^ n * (1 + π) ^ n := mul_le_mul_of_nonneg_left hbern hpos
      _ ≤ 1 := hprod
  have hnπ : 0 ≤ (n : ℝ) * π := by positivity
  have h2 : (n : ℝ) * π ≤ 2 * δ := by nlinarith
  rw [le_div_iff₀ (by linarith)]
  linarith
