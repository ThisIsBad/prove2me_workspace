import Mathlib
import Definitions.Def_OnlineSetCover_LowerBound_Game
import Definitions.Def_OnlineSetCover_LowerBound_BitFamily

namespace OnlineSetCover.LowerBound

/-- Proposition 4.1 (Alon et al. 2009, p. 368). On `X = {0, …, 2^k − 1}` with the family
`F = {F_1, …, F_k}` of bit sets, (1) `|F| = k`; (2) against every valid deterministic online
algorithm the adversary has a nonempty arrival sequence that one set of `F` covers (so
`OPT = 1`) while the algorithm chooses at least `k = k · OPT` sets; (3) some valid deterministic
online algorithm chooses at most `k · |C|` sets on every arrival sequence and every offline
cover `C` of it, i.e. has competitive ratio at most `k`. -/
theorem proposition_4_1 (k : ℕ) (hk : 0 < k) :
    (bitFamily k).card = k ∧
    (∀ A : OnlineAlg (Fin (2 ^ k)), IsValid (bitFamily k) A →
      ∃ σ : List (Fin (2 ^ k)), σ ≠ [] ∧
        (∃ S ∈ bitFamily k, ∀ x ∈ σ, x ∈ S) ∧ k ≤ cost A σ) ∧
    (∃ A : OnlineAlg (Fin (2 ^ k)), IsValid (bitFamily k) A ∧
      ∀ (σ : List (Fin (2 ^ k))) (C : Finset (Finset (Fin (2 ^ k)))),
        IsCoverOf (bitFamily k) C σ → cost A σ ≤ k * C.card) := by sorry

end OnlineSetCover.LowerBound

