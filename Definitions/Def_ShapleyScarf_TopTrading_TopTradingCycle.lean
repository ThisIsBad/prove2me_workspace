import Mathlib

namespace ShapleyScarf.TopTrading

/-- **Top trading cycle for `R`** (Shapley–Scarf 1974, §6, pp. 113–114). A set `S` with
`∅ ⊂ S ⊆ R` whose members form a single cycle `i₁ → i₂ → ⋯ → i_s → i₁` of the successor map
`next` (`next` maps `S` into `S` and every member of `S` reaches every other by iterating `next`),
such that each member `i` of `S` likes the good of its successor `next i` at least as well as any
other good in `R`. A single trader with `next i = i` is allowed. -/
def IsTopTradingCycle {N : Type*} (A : N → N → ℝ) (R S : Finset N) (next : N → N) : Prop :=
  S.Nonempty ∧ S ⊆ R ∧ (∀ i ∈ S, next i ∈ S) ∧
    (∀ i ∈ S, ∀ i' ∈ S, ∃ k : ℕ, next^[k] i = i') ∧
    ∀ i ∈ S, ∀ j ∈ R, A i j ≤ A i (next i)

/-- **Top-trading-cycle partition** (Shapley–Scarf 1974, §6, p. 114): `N = S¹ ∪ S² ∪ ⋯ ∪ Sᵖ`,
where `S^{j+1}` (Lean index `j : Fin p`, counted from `0`) is the set of traders with
`stage i = j`, and it is a top trading cycle, for the successor map `next`, for the traders not
yet removed, `N − (S¹ ∪ ⋯ ∪ Sʲ) = {i | j ≤ stage i}`. Every trader lies in exactly one stage, and
`next i` is trader `i`'s cyclic successor in his own cycle. -/
structure TTCPartition {N : Type*} [Fintype N] [DecidableEq N] (A : N → N → ℝ) where
  /-- the number of cycles -/
  p : ℕ
  /-- the cycle containing each trader (`0` is the first cycle `S¹`) -/
  stage : N → Fin p
  /-- each trader's cyclic successor in his cycle -/
  next : N → N
  /-- the `j`-th cycle is a top trading cycle for the traders of stage `≥ j` -/
  isTopTradingCycle : ∀ j : Fin p,
    IsTopTradingCycle A (Finset.univ.filter fun i => j ≤ stage i)
      (Finset.univ.filter fun i => stage i = j) next

end ShapleyScarf.TopTrading
