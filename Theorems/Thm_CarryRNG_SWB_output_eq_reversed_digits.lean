import Definitions.Def_CarryRNG_SWB_out
import Definitions.Def_CarryRNG_AWC_digit
import Definitions.Def_CarryRNG_SWB_modulus
import Definitions.Def_CarryRNG_AWC_zeroSeed
import Definitions.Def_CarryRNG_AWC_topSeed

namespace CarryRNG.SWB

/-- Section 4.3: every generated finite block, read backwards, starts the expansion of
a proper fraction with denominator `m = b^r - b^s + 1`. -/
theorem output_eq_reversed_digits (b : ℕ) (L : CarryRNG.AWC.Lags) (hb : 2 ≤ b)
    (z : CarryRNG.AWC.State b L.r) (hz : z ≠ CarryRNG.AWC.topSeed b L.r hb) (C : ℕ) (hC : L.r + 1 ≤ C) :
    ∃ k : ℕ, k < modulus b L ∧ (0 < k ↔ z ≠ CarryRNG.AWC.zeroSeed b L.r hb) ∧
      ∀ n : ℕ, L.r + 1 ≤ n → n ≤ C →
        out b L hb z n = CarryRNG.AWC.digit b (modulus b L) k (C + 1 - n) := by sorry

end CarryRNG.SWB

