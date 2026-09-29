import Mathlib

namespace LubyMIS.Derandomized

/-- TECHNICAL LEMMA (Luby 1986, §3.4, p. 1043). Let `p₁ ≥ ⋯ ≥ pₙ ≥ 0` and `c > 0`. With
`α_l = ∑_{j=1}^{l} p_j`, `β_l = ∑_{j=1}^{l} ∑_{k=j+1}^{l} p_j p_k`, `γ_l = α_l − c β_l`, some
`1 ≤ l ≤ n` has `γ_l ≥ ½ · min {α_n, 1/c}`. -/
theorem technical_lemma (n : ℕ) (hn : 1 ≤ n) (p : ℕ → ℝ)
    (hanti : ∀ j k : ℕ, 1 ≤ j → j ≤ k → k ≤ n → p k ≤ p j) (hpn : 0 ≤ p n)
    (c : ℝ) (hc : 0 < c) :
    ∃ l : ℕ, 1 ≤ l ∧ l ≤ n ∧
      (∑ j ∈ Finset.Icc 1 l, p j) - c * (∑ j ∈ Finset.Icc 1 l, ∑ k ∈ Finset.Ioc j l, p j * p k)
        ≥ 1 / 2 * min (∑ j ∈ Finset.Icc 1 n, p j) (1 / c) := by sorry

end LubyMIS.Derandomized
