import Mathlib
import Definitions.Def_FranklKupavskii2022_EMC_matchingNumber
import Definitions.Def_FranklKupavskii2022_EMC_IsInitial

open FinsetFamily

namespace FranklKupavskii2022.EMC

/-- Corollary 7 (Frankl–Kupavskii, arXiv:1806.08855v3, p. 4): for every initial
`G ⊂ \binom{[m]}{k}` such that `ν(∂G) ≤ s` and every `F ∈ G` there exists some `i`, `1 ≤ i < k`,
such that `|F ∩ [i(s + 1) − 1]| ≥ i + 1` (13).

**Formalization Note.** `k ≥ 2` is added: at `k = 1`, `G = {{1}}` is initial with `∂G = {∅}` and
`ν(∂G) = 1 ≤ s`, but no `i` with `1 ≤ i < 1` exists; the paper's proof applies (10) to
`(k − 1)`-sets, i.e. uses `k − 1 ≥ 1`. `1 ≤ s` is the Sect. 1 standing assumption. -/
theorem shadow_dense_prefix (m k s : ℕ) (hk : 2 ≤ k) (hs : 1 ≤ s) (G : Finset (Finset ℕ))
    (hG : G ⊆ (Finset.Icc 1 m).powersetCard k) (hinit : IsInitial m k G)
    (hν : matchingNumber (∂ G) ≤ s) :
    ∀ F ∈ G, ∃ i, 1 ≤ i ∧ i < k ∧ i + 1 ≤ (F ∩ Finset.Icc 1 (i * (s + 1) - 1)).card := by sorry

end FranklKupavskii2022.EMC
