import Mathlib

namespace ProcessingNetworks.LyapunovCriteria

open scoped NNReal

/-- Definition 8.1 (Lipschitz continuity), Dai & Harrison p. 135 (PDF p. 151): `g` is Lipschitz
on `s` if, for every bounded set `B`, there is a constant `κ(B) > 0` such that
`|g(x) - g(y)| ≤ κ(B)|x-y|` for `x, y ∈ s ∩ B` — i.e. `g` is `LipschitzOnWith` some constant on
every bounded subset of `s`. Stated for arbitrary (pseudo)metric domain/codomain types so that it
covers both `g : ℝ^d → ℝ^m` and `g : ℝ^m → ℝ` (Lemma 8.2) with the same definition, matching the
book's own remark that "the same definition applies when `ℝ^d` is replaced by `ℝ^d_+`" (take
`s = Set.univ` for the unrestricted domain, `s = {z | ∀ i, 0 ≤ z i}` for `ℝ^d_+`). -/
def IsLipschitzOn {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β] (g : α → β)
    (s : Set α) : Prop :=
  ∀ B : Set α, Bornology.IsBounded B → ∃ K : ℝ≥0, LipschitzOnWith K g (s ∩ B)

/-- Definition 8.1's globally Lipschitz continuity: the constant `κ(B)` can be taken independent
of `B`, i.e. `g` is `LipschitzOnWith` a single constant on the whole of `s`. -/
def IsGloballyLipschitzOn {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β] (g : α → β)
    (s : Set α) : Prop :=
  ∃ K : ℝ≥0, LipschitzOnWith K g s

end ProcessingNetworks.LyapunovCriteria
