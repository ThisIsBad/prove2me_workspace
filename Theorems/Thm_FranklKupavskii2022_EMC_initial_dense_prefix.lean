import Mathlib
import Definitions.Def_FranklKupavskii2022_EMC_matchingNumber
import Definitions.Def_FranklKupavskii2022_EMC_IsInitial

namespace FranklKupavskii2022.EMC

/-- Proposition 4 (Frankl–Kupavskii, arXiv:1806.08855v3, p. 4): if `F ⊂ \binom{[m]}{k}` is initial
and `ν(F) ≤ s`, then `(s + 1, 2(s + 1), …, k(s + 1)) ∉ F`; consequently, for every `F ∈ F` there
is some `i`, `1 ≤ i ≤ k`, with `|F ∩ [i(s + 1) − 1]| ≥ i` (10).

**Formalization Note.** The set `(s+1, 2(s+1), …, k(s+1))` is the image of `j ↦ j(s+1)` on
`Finset.Icc 1 k`; `[i(s+1) − 1] = Finset.Icc 1 (i * (s + 1) - 1)` (exact for `i ≥ 1`). The
Sect. 1 standing assumption "positive integers k, s" is kept as `1 ≤ k`, `1 ≤ s`; at `k = 0` the
first claim fails for `F = {∅}`. -/
theorem initial_dense_prefix (m k s : ℕ) (hk : 1 ≤ k) (hs : 1 ≤ s) (F : Finset (Finset ℕ))
    (hF : F ⊆ (Finset.Icc 1 m).powersetCard k) (hinit : IsInitial m k F)
    (hν : matchingNumber F ≤ s) :
    (Finset.Icc 1 k).image (fun j => j * (s + 1)) ∉ F ∧
      ∀ A ∈ F, ∃ i, 1 ≤ i ∧ i ≤ k ∧ i ≤ (A ∩ Finset.Icc 1 (i * (s + 1) - 1)).card := by sorry

end FranklKupavskii2022.EMC
