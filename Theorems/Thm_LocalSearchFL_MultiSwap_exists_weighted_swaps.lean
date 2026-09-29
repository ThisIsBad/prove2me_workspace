import Mathlib
import Definitions.Def_LocalSearchFL_MultiSwap_capture

namespace LocalSearchFL.MultiSwap

/-- The weighted swaps of §3.4 (pp. 552–553). If `|S| = |O|` and `p ≥ 1`, there is a finite set
`W` of swaps `⟨A, B⟩` with `A ⊆ S`, `B ⊆ O`, `|A| = |B| ≤ p`, and positive real weights `w`, such
that
1. for every `o ∈ O`, the weights of the swaps `⟨A, B⟩` with `o ∈ B` sum to exactly one;
2. for every `s ∈ S`, the weights of the swaps `⟨A, B⟩` with `s ∈ A` sum to at most `(p + 1)/p`;
3. if `⟨A, B⟩ ∈ W`, then `capture(A) ⊆ B`.
Moreover (from the construction: the sets `A` are blocks `A_i` of the partition of Claim 3.1 or
single facilities of a block) the deleted sets of any two swaps are equal or disjoint. -/
theorem exists_weighted_swaps {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa]
    (σS σO : Cl → Fa) (S O : Finset Fa) (hcard : S.card = O.card) (p : ℕ) (hp : 1 ≤ p) :
    ∃ (W : Finset (Finset Fa × Finset Fa)) (w : Finset Fa × Finset Fa → ℝ),
      (∀ AB ∈ W, AB.1 ⊆ S ∧ AB.2 ⊆ O ∧ AB.1.card = AB.2.card ∧ AB.1.card ≤ p ∧ 0 < w AB) ∧
      (∀ o ∈ O, ∑ AB ∈ W.filter (fun AB => o ∈ AB.2), w AB = 1) ∧
      (∀ s ∈ S, ∑ AB ∈ W.filter (fun AB => s ∈ AB.1), w AB ≤ ((p : ℝ) + 1) / p) ∧
      (∀ AB ∈ W, capture σS σO O AB.1 ⊆ AB.2) ∧
      (∀ AB ∈ W, ∀ AB' ∈ W, AB.1 = AB'.1 ∨ Disjoint AB.1 AB'.1) := by sorry

end LocalSearchFL.MultiSwap

