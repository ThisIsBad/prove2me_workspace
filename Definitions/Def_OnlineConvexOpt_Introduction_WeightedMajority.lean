import Mathlib

namespace OnlineConvexOpt.Introduction

variable {N : ℕ}

/-- One run of the Weighted Majority algorithm (§1.3.1, p. 9) with `N` experts and decay
parameter `ε`, against adversarially chosen expert predictions `expertPredict` and true
outcomes `outcome` (the book's actions `A`/`B` represented by `true`/`false`). `W` are the
algorithm's weights: `W 0 i = 1` for every expert, and at each round the weight of an expert
who erred is scaled by `(1 - ε)` while a correct expert's weight is unchanged. `algPredict` is
fixed by the majority-vote rule: the algorithm predicts `true` exactly when the total weight
currently backing `true` is at least the total weight backing `false`
(`a_t = A` if `W_t(A) ≥ W_t(B)` else `B`). -/
structure IsWeightedMajorityRun (ε : ℝ) (expertPredict : ℕ → Fin N → Bool)
    (outcome : ℕ → Bool) (W : ℕ → Fin N → ℝ) (algPredict : ℕ → Bool) : Prop where
  weight_init : ∀ i, W 0 i = 1
  weight_update : ∀ t i, W (t + 1) i =
    if expertPredict t i = outcome t then W t i else W t i * (1 - ε)
  predict_rule : ∀ t, algPredict t = true ↔
    (∑ i ∈ Finset.univ.filter (fun i => expertPredict t i = true), W t i) ≥
    (∑ i ∈ Finset.univ.filter (fun i => expertPredict t i = false), W t i)

end OnlineConvexOpt.Introduction
