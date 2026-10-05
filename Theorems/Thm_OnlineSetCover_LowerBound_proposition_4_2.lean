import Mathlib
import Definitions.Def_OnlineSetCover_LowerBound_Game

namespace OnlineSetCover.LowerBound

/-- Proposition 4.2 (Alon et al. 2009, p. 369). For positive integers `k, r` and `n, m` with
`n ≥ 2^{k+1} k r²` and `2^{2^k k r²} ≥ m ≥ C(k r², r) k^r`, there is a family `𝓕` of exactly `m`
distinct subsets of `X = Fin n` such that against every valid deterministic online algorithm
`A` the adversary has a nonempty arrival sequence `σ` that a single member of `𝓕` covers
(`OPT(σ) = 1`) while `A` chooses at least `k r` sets; in particular the competitive ratio of
every deterministic online algorithm on `(X, 𝓕)` is at least `k r`. -/
theorem proposition_4_2 (k r n m : ℕ) (hk : 0 < k) (hr : 0 < r)
    (hn : 2 ^ (k + 1) * k * r ^ 2 ≤ n)
    (hm_lo : (k * r ^ 2).choose r * k ^ r ≤ m)
    (hm_hi : m ≤ 2 ^ (2 ^ k * k * r ^ 2)) :
    ∃ 𝓕 : Finset (Finset (Fin n)), 𝓕.card = m ∧
      ∀ A : OnlineAlg (Fin n), IsValid 𝓕 A →
        ∃ σ : List (Fin n), σ ≠ [] ∧ (∃ S ∈ 𝓕, ∀ x ∈ σ, x ∈ S) ∧ k * r ≤ cost A σ := by sorry

end OnlineSetCover.LowerBound

