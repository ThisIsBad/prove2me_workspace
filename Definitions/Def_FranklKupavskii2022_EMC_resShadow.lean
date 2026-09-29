import Mathlib

open FinsetFamily

namespace FranklKupavskii2022.EMC

/-- The index `i_F` (Frankl–Kupavskii, arXiv:1806.08855v3, Sect. 2.1, p. 4): "For a set F, let us
denote i_F the largest i for which (13) holds", where (13) is
`|F ∩ [i(s + 1) − 1]| ≥ i + 1` with `1 ≤ i < k`.

**Formalization Note.** `[i(s+1) − 1] = Finset.Icc 1 (i * (s + 1) - 1)`; for `i ≥ 1` the natural
subtraction is exact. If no `i` with `1 ≤ i < k` satisfies (13) the value is `0` (the `sup` of the
empty set); Corollary 7 of the paper shows this does not happen for members of an initial
`k`-uniform family `G` with `ν(∂G) ≤ s` and `k ≥ 2`. -/
def iF (s k : ℕ) (F : Finset ℕ) : ℕ :=
  ((Finset.Ico 1 k).filter (fun i => i + 1 ≤ (F ∩ Finset.Icc 1 (i * (s + 1) - 1)).card)).sup id

/-- The tail `T(F) := F \ [i_F(s + 1) − 1]` (Frankl–Kupavskii, arXiv:1806.08855v3, Sect. 2.1,
p. 4). It depends only on `F` (and on the parameters `s`, `k`). -/
def tail (s k : ℕ) (F : Finset ℕ) : Finset ℕ :=
  F \ Finset.Icc 1 (iF s k F * (s + 1) - 1)

/-- The layer `G_i` (Frankl–Kupavskii, arXiv:1806.08855v3, Sect. 2.1, p. 4): "Let us split
G := ⊔_{i=1}^{k−1} G_i, where G_i is the subfamily of all sets F satisfying i_F = i." -/
def layer (s k : ℕ) (G : Finset (Finset ℕ)) (i : ℕ) : Finset (Finset ℕ) :=
  G.filter (fun F => iF s k F = i)

/-- The restricted shadow (Frankl–Kupavskii, arXiv:1806.08855v3, Sect. 2.1, p. 4):
`∂_res G := {F′ ∈ ∂G : ∃ F ∈ G s.t. T(F) ⊂ F′ ⊂ F}` (the paper's `⊂` is non-strict inclusion).
The paper's `∂_res G_i` is `resShadow s k (layer s k G i)`. -/
def resShadow (s k : ℕ) (G : Finset (Finset ℕ)) : Finset (Finset ℕ) :=
  (∂ G).filter (fun F' => ∃ F ∈ G, tail s k F ⊆ F' ∧ F' ⊆ F)

end FranklKupavskii2022.EMC
