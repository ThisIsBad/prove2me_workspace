import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance

open KellyStochasticNetworks

theorem solution {S : Type*} (π : S → ℝ) (q : S → S → ℝ)
    (hπ : ∀ j, 0 < π j) : reversedRates π q = q ↔ DetailedBalance π q := by
  constructor
  · intro hq j k
    have hjk := congrFun (congrFun hq j) k
    simp only [reversedRates] at hjk
    rw [div_eq_iff (hπ j).ne'] at hjk
    linarith
  · intro hdb
    funext j k
    simp only [reversedRates]
    rw [div_eq_iff (hπ j).ne', ← hdb j k]
    ring
