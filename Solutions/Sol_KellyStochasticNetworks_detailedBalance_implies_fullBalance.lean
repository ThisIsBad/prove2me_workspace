import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance

open KellyStochasticNetworks

theorem solution {S : Type*} (π : S → ℝ) (q : S → S → ℝ)
    (h : DetailedBalance π q) : FullBalance π q := by
  intro j
  have hk : (fun k => π k * q k j) = fun k => π j * q j k := by
    funext k
    exact (h j k).symm
  rw [hk, tsum_mul_left]
