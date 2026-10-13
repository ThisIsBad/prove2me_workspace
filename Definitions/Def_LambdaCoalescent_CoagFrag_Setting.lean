import Mathlib
import Definitions.Def_LambdaCoalescent_Rates_Setting

namespace LambdaCoalescent.CoagFrag

open MeasureTheory

/-- `R_n`: the restriction of a partition of `ℕ` to `[n]`, encoded as `Fin n = {0, …, n-1}`. -/
def restrict (n : ℕ) (π : Setoid ℕ) : Setoid (Fin n) := π.comap Fin.val

open Classical in
/-- The blocks of a partition `π` of `[n]`, as a finset of (nonempty) finsets. -/
noncomputable def blocks {n : ℕ} (π : Setoid (Fin n)) : Finset (Finset (Fin n)) :=
  Finset.univ.image (fun i => Finset.univ.filter (fun j => π i j))

/-- The multiset `{n₁, …, n_k}` of block sizes of a partition of `[n]`. -/
noncomputable def blockSizes {n : ℕ} (π : Setoid (Fin n)) : Multiset ℕ :=
  (blocks π).val.map Finset.card

open Classical in
/-- For `π₁ ≤ π₂` (π₁ refines π₂): the multiset `{j₁, …, j_k}` where `j_i = #{ℓ : A_ℓ ⊆ B_i}` is the
number of `π₁`-blocks inside the `i`-th block `B_i` of `π₂` (Lemma 34). -/
noncomputable def coagCounts {n : ℕ} (π₁ π₂ : Setoid (Fin n)) : Multiset ℕ :=
  (blocks π₂).val.map (fun B => ((blocks π₁).filter (fun A => A ⊆ B)).card)

open Classical in
/-- For `π₁ ≤ π₂`: for each block `B_i` of `π₂`, the multiset `{a_{i,1}, …, a_{i,j_i}}` of sizes of the
`π₁`-blocks inside `B_i` (Lemma 35). -/
noncomputable def fragSizes {n : ℕ} (π₁ π₂ : Setoid (Fin n)) : Multiset (Multiset ℕ) :=
  (blocks π₂).val.map (fun B => ((blocks π₁).filter (fun A => A ⊆ B)).val.map Finset.card)

open Classical in
/-- The least element of the block of `π` containing `i`. -/
noncomputable def leastElt (π : Setoid ℕ) (i : ℕ) : ℕ :=
  Nat.find (⟨i, π.refl i⟩ : ∃ m, π m i)

open Classical in
/-- The 0-based position of the block of `i` among the blocks of `π` listed in increasing order of
their least elements (the block `A₁` of Definition 5 has index `0`). -/
noncomputable def blockIndex (π : Setoid ℕ) (i : ℕ) : ℕ :=
  ((Finset.range (leastElt π i)).filter (fun m => leastElt π m = m)).card

/-- Definition 5 (with `n = ∞`): the `γ`-coagulation of `π`. If `π = {A₁, A₂, …}` and
`γ = {B₁, B₂, …}`, its blocks are the nonempty sets `⋃_{j ∈ B_i} A_j`: `i` and `j` are together iff the
indices of their `π`-blocks lie in the same block of `γ`. -/
noncomputable def coag (π γ : Setoid ℕ) : Setoid ℕ := γ.comap (blockIndex π)

/-- Definition 11: the refinement of `π'` whose restriction to the `m`-th block of `π'` (0-based, in
increasing order of least elements) is the restriction of `Γ m` to that block: `i ~ j` iff `i, j` are
in the same block of `π'`, with index `m`, and `Γ m` relates them. -/
noncomputable def frag (π' : Setoid ℕ) (Γ : ℕ → Setoid ℕ) : Setoid ℕ :=
  Setoid.ker (fun i => (blockIndex π' i, {x | Γ (blockIndex π' i) i x}))

/-- The EPF (15) of an `(α, θ)` partition, with the factors of `α` and `θ` cancelled:
`p_{α,θ}(n₁, …, n_k) = (∏_{i=1}^{k-1} (θ + iα)) / [θ+1]_{n-1} · ∏_{i=1}^{k} [1-α]_{n_i - 1}`,
where `k` is the number of blocks, `n = n₁ + ⋯ + n_k`, and `[x]_m = x (x+1) ⋯ (x+m-1)`. -/
noncomputable def pdEPF (α θ : ℝ) (s : Multiset ℕ) : ℝ :=
  (∏ i ∈ Finset.Ico 1 s.card, (θ + (i : ℝ) * α)) / (ascPochhammer ℝ (s.sum - 1)).eval (θ + 1) *
    (s.map (fun m => (ascPochhammer ℝ (m - 1)).eval (1 - α))).prod

/-- `μ` is the law of an exchangeable random partition of `ℕ` with EPF `p`: for every `n` and every
partition `s` of `[n]`, `μ {π : R_n π = s} = p(sizes of the blocks of s)`. -/
def IsEPFLaw (p : Multiset ℕ → ℝ) (μ : Measure LambdaCoalescent.Rates.PInf) : Prop :=
  ∀ (n : ℕ) (s : Setoid (Fin n)), μ.real {π : LambdaCoalescent.Rates.PInf | restrict n π = s} = p (blockSizes s)

end LambdaCoalescent.CoagFrag
