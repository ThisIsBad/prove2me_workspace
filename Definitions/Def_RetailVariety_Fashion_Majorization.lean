import Mathlib

namespace RetailVariety.Fashion

/-- Majorization, Definition 1 (van Ryzin & Mahajan 1999, p. 1505). For `x, y ∈ ℝⁿ`, `x ≺ y`
(`x` is majorized by `y`) iff, writing `x_[1] ≥ ⋯ ≥ x_[n]` for the decreasing rearrangement,
`∑_{i=1}^n x_[i] = ∑_{i=1}^n y_[i]` and `∑_{i=1}^k x_[i] ≤ ∑_{i=1}^k y_[i]` for `k = 1, …, n − 1`.

The decreasing rearrangement is `x ∘ σx` for a permutation `σx` with `x ∘ σx` antitone (the
paper's `[i]`); such a permutation always exists and the partial sums of `x ∘ σx` do not depend on
which one is chosen, so the existential form agrees with the universal one. The first `k` entries
(0-based indices `< k`) of the rearranged vector are summed. -/
def Majorized {n : ℕ} (x y : Fin n → ℝ) : Prop :=
  ∃ σx σy : Equiv.Perm (Fin n),
    Antitone (x ∘ σx) ∧ Antitone (y ∘ σy) ∧
    ∑ i, x (σx i) = ∑ i, y (σy i) ∧
    ∀ k : ℕ, 1 ≤ k → k < n →
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), x (σx i) ≤
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), y (σy i)

/-- Definition 2 (p. 1505): a merchandise category `v` is *more fashionable* than `w` if
`(v_1, …, v_n) ≺ (w_1, …, w_n)`. -/
def MoreFashionable {n : ℕ} (v w : Fin n → ℝ) : Prop :=
  Majorized v w

end RetailVariety.Fashion
