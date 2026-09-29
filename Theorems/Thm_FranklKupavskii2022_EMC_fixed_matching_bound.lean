import Mathlib
import Definitions.Def_FranklKupavskii2022_EMC_tMatchings
import Definitions.Def_FranklKupavskii2022_EMC_CrossDependent
import Definitions.Def_FranklKupavskii2022_EMC_Nested

namespace FranklKupavskii2022.EMC

/-- Lemma 18 (Frankl–Kupavskii, arXiv:1806.08855v3, p. 11): let `1 ≤ x, q ≤ s + 1` and
`t ≥ s + x + 1`, `t ∈ ℕ`. Let the families `F_1, …, F_{s+1} ⊂ \binom{Y}{l}` be cross-dependent and
nested, and suppose that `|Y| ≥ tl`. Fix any `t`-matching `B` of `l`-element sets in `Y`. Then
`|B ∩ F_1| + … + |B ∩ F_s| + q|B ∩ F_{s+1}| ≤ st + q|B ∩ F_{s+1}| − sx` (30) for
`|B ∩ F_{s+1}| ≥ x`, and
`|B ∩ F_1| + … + |B ∩ F_s| + q|B ∩ F_{s+1}| ≤ st − |B ∩ F_{s+1}|(x − q|B ∩ F_{s+1}|/(s+1))` (31)
for `|B ∩ F_{s+1}| ≤ x`.

**Formalization Note.** `x, q` are real; "1 ≤ x, q ≤ s + 1" is read as `1 ≤ x ≤ s + 1` and
`1 ≤ q ≤ s + 1`. The families are `Fam 1, …, Fam (s + 1)`. The matching is an ordered tuple
`B : Fin t → Finset ℕ` of pairwise disjoint `l`-subsets of `Y`, and `|B ∩ F_i|` is `eta (Fam i) B`,
the number of positions `j` with `B_j ∈ F_i` (for `l ≥ 1` the `B_j` are distinct, so this is the
size of the set intersection). -/
theorem fixed_matching_bound (s t l : ℕ) (x q : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ s + 1) (hq1 : 1 ≤ q)
    (hq2 : q ≤ s + 1) (ht : (s : ℝ) + x + 1 ≤ t) (Y : Finset ℕ) (Fam : ℕ → Finset (Finset ℕ))
    (hFam : ∀ i ∈ Finset.Icc 1 (s + 1), Fam i ⊆ Y.powersetCard l)
    (hcross : CrossDependent s Fam) (hnest : Nested s Fam) (hY : t * l ≤ Y.card)
    (B : Fin t → Finset ℕ) (hB : ∀ j, B j ∈ Y.powersetCard l)
    (hBdisj : ∀ i j : Fin t, i ≠ j → Disjoint (B i) (B j)) :
    (x ≤ (eta (Fam (s + 1)) B : ℝ) →
        ∑ i ∈ Finset.Icc 1 s, (eta (Fam i) B : ℝ) + q * eta (Fam (s + 1)) B ≤
          s * t + q * eta (Fam (s + 1)) B - s * x) ∧
      ((eta (Fam (s + 1)) B : ℝ) ≤ x →
        ∑ i ∈ Finset.Icc 1 s, (eta (Fam i) B : ℝ) + q * eta (Fam (s + 1)) B ≤
          s * t - eta (Fam (s + 1)) B * (x - q * eta (Fam (s + 1)) B / (s + 1))) := by sorry

end FranklKupavskii2022.EMC
