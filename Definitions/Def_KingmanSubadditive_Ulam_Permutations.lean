import Mathlib

namespace KingmanSubadditive.Ulam

open Filter Topology

/-- A set `s` of positions is **ascending** for the permutation `σ` of `{1, …, n}` (here `Fin n`)
if `σ` is strictly increasing on it: whenever `i < j` lie in `s`, `σ i < σ j`. A `k`-element
ascending set `{i₁ < ⋯ < i_k}` is exactly a sequence with `π(i₁) < ⋯ < π(i_k)` in the sense of
Kingman, *Subadditive ergodic theory*, Ann. Probab. 1(6):883–899 (1973), §2.4, pp. 893–894. -/
def IsAscendingOn {n : ℕ} (σ : Equiv.Perm (Fin n)) (s : Finset (Fin n)) : Prop :=
  ∀ i ∈ s, ∀ j ∈ s, i < j → σ i < σ j

instance {n : ℕ} (σ : Equiv.Perm (Fin n)) (s : Finset (Fin n)) :
    Decidable (IsAscendingOn σ s) := by
  unfold IsAscendingOn; infer_instance

/-- `l(π)`, the length of the longest ascending sequence in `σ ∈ 𝒮_n` (Kingman 1973, §2.4,
pp. 893–894): the largest `k` for which there exist `1 ≤ i₁ < ⋯ < i_k ≤ n` with
`σ(i₁) < ⋯ < σ(i_k)`, i.e. the largest cardinality of an ascending set of positions.

**Formalization Note** The paper's permutation is called `π`; it is `σ` here because `π` is
`Real.pi` in Theorem 8. `𝒮_n` is `Equiv.Perm (Fin n)`. The empty set is ascending, so `lis σ`
is well defined (it is `0` only for `n = 0`). -/
def lis {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin n))).filter (fun s => IsAscendingOn σ s)).sup Finset.card

/-- `ν`, the number of ascending sequences `i₁ < i₂ < ⋯ < i_k ≤ n` of length `k` in `σ`
(Kingman 1973, §2.4, proof of Theorem 8, p. 896): the number of `k`-element sets of positions
on which `σ` is strictly increasing. -/
def numAscending {n : ℕ} (k : ℕ) (σ : Equiv.Perm (Fin n)) : ℕ :=
  (((Finset.univ : Finset (Fin n)).powersetCard k).filter (fun s => IsAscendingOn σ s)).card

/-- The uniform distribution on `𝒮_n` (Kingman 1973, §2.4, p. 894): the probability of an
event `A ⊆ 𝒮_n` is `#A / n!`, the proportion of the `n!` permutations of `{1, …, n}` lying
in `A`. -/
noncomputable def unifProb (n : ℕ) (A : Equiv.Perm (Fin n) → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter A).card : ℝ) / (Nat.factorial n : ℝ)

/-- `n^{−½} l(π_n)` **converges in probability to `c`** when `π_n` is uniformly distributed
over `𝒮_n` (Kingman 1973, §2.4, Theorem 7, p. 895): for every `ε > 0`,
`P{|n^{−½} l(π_n) − c| > ε} → 0` as `n → ∞`, the probability being the uniform one on `𝒮_n`.

**Formalization Note** Convergence in probability depends only on the law of each `π_n`
(the paper says so on p. 895), so it is stated through the counting probability `unifProb`.
At `n = 0` Lean reads `l(π)/√0` as `0`; a single index does not affect a limit. -/
def ConvergesInProbUniform (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto (fun n : ℕ => unifProb n (fun σ => ε < |(lis σ : ℝ) / Real.sqrt n - c|))
      atTop (𝓝 0)

/-- The exponent of the Stirling estimate (2.4.8) (Kingman 1973, §2.4, proof of Theorem 8,
p. 896): `2α + (b − α) log (b − α) − α log α − b log b`, the paper's left side of (2.4.8)
with its `β` renamed `b` (the paper also uses `β` for the constant of Theorem 8). It is used
only for `0 < α < b`, where every logarithm has a positive argument. -/
noncomputable def stirlingExponent (α b : ℝ) : ℝ :=
  2 * α + (b - α) * Real.log (b - α) - α * Real.log α - b * Real.log b

end KingmanSubadditive.Ulam
