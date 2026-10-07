import Mathlib

namespace ShapleyScarf.TopTrading

/-- **Core allocation** (Shapley–Scarf 1974, §2, p. 107), for the housing market with traders `N`
and preference matrix `A` (`A i j` = trader `i`'s ordinal value of item `j`, the good brought by
trader `j`; ties allowed). The allocation gives trader `i` the item `σ i`; it is a permutation
allocation (`σ` bijective), and no nonempty coalition `S` has an `S`-permutation `τ` (a map
sending `S` injectively into `S`, i.e. a reshuffling of the items of `S` among the members of
`S`) that makes **every** member of `S` strictly better off. -/
def IsCoreAllocation {N : Type*} (A : N → N → ℝ) (σ : N → N) : Prop :=
  Function.Bijective σ ∧
    ¬ ∃ (S : Finset N) (τ : N → N), S.Nonempty ∧ (∀ i ∈ S, τ i ∈ S) ∧
        Set.InjOn τ (S : Set N) ∧ ∀ i ∈ S, A i (σ i) < A i (τ i)

/-- **Competitive allocation** (Shapley–Scarf 1974, §1 p. 105 and §6 p. 114). The permutation
allocation `σ` is competitive at the price vector `price` (`price k` = price of item `k`) if every
trader `i`, selling his own item for `price i`, can afford the item `σ i` he receives
(`price (σ i) ≤ price i`) and no affordable item is better for him than `σ i`. Supply equals
demand because `σ` is a bijection. -/
def IsCompetitive {N : Type*} (A : N → N → ℝ) (σ : N → N) (price : N → ℝ) : Prop :=
  Function.Bijective σ ∧
    ∀ i, price (σ i) ≤ price i ∧ ∀ k, price k ≤ price i → A i k ≤ A i (σ i)

end ShapleyScarf.TopTrading
