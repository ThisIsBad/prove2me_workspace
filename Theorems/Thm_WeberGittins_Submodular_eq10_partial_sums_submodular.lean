import Definitions.Def_WeberGittins_Submodular_PartialInterleavedSum

namespace WeberGittins.Submodular

/-- Weber (1992), proof of Theorem 4, eq. (10), p. 1030: for nonincreasing, nonnegative
prevailing-charge sequences `H j`, the partial interleaved sums are submodular in the set of
bandits: `U_t(I ∩ J) + U_t(I ∪ J) ≤ U_t(I) + U_t(J)` for all `t ≥ 0`. -/
theorem eq10_partial_sums_submodular {n : ℕ} (H : Fin n → ℕ → ℝ)
    (hanti : ∀ j, Antitone (H j)) (hnonneg : ∀ j k, 0 ≤ H j k)
    (I J : Finset (Fin n)) (t : ℕ) :
    partialInterleavedSum H (I ∩ J) t + partialInterleavedSum H (I ∪ J) t ≤
      partialInterleavedSum H I t + partialInterleavedSum H J t := by sorry

end WeberGittins.Submodular

