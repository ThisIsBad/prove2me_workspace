import Mathlib
import Definitions.Def_FranklKupavskii2022_EMC_matchingNumber
import Definitions.Def_FranklKupavskii2022_EMC_IsInitial
import Definitions.Def_FranklKupavskii2022_EMC_resShadow

open FinsetFamily

namespace FranklKupavskii2022.EMC

/-- Lemma 8 (Frankl–Kupavskii, arXiv:1806.08855v3, p. 5): if `G ⊂ \binom{[m]}{k}` satisfies
`ν(∂G) ≤ s` then `|∂_res G_i| ≥ \frac{i+1}{is} |G_i|` (14). Moreover, `∂_res G_i` are disjoint for
different `i`.

**Formalization Note.** Sect. 2.1 (p. 4) works throughout "with an initial family
G ⊂ \binom{[m]}{k} which satisfies ν(∂G) ≤ s", and `i_F` is defined through Corollary 7, so
`IsInitial m k G` is a hypothesis. `k ≥ 2` (as for Corollary 7) and `1 ≤ s` (Sect. 1) are
added. (14) is stated for `1 ≤ i < k`, the range of the decomposition `G = ⊔_{i=1}^{k−1} G_i`;
the disjointness is stated for distinct `i, j` in the same range. `G_i = layer s k G i`,
`∂_res G_i = resShadow s k (layer s k G i)`. -/
theorem restricted_shadow_layer (m k s : ℕ) (hk : 2 ≤ k) (hs : 1 ≤ s) (G : Finset (Finset ℕ))
    (hG : G ⊆ (Finset.Icc 1 m).powersetCard k) (hinit : IsInitial m k G)
    (hν : matchingNumber (∂ G) ≤ s) :
    (∀ i, 1 ≤ i → i < k →
        ((i : ℝ) + 1) / ((i : ℝ) * s) * ((layer s k G i).card : ℝ) ≤
          ((resShadow s k (layer s k G i)).card : ℝ)) ∧
      ∀ i j, 1 ≤ i → i < k → 1 ≤ j → j < k → i ≠ j →
        Disjoint (resShadow s k (layer s k G i)) (resShadow s k (layer s k G j)) := by sorry

end FranklKupavskii2022.EMC
