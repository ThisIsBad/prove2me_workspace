import Mathlib
import Definitions.Def_FranklKupavskii2022_EMC_matchingNumber
import Definitions.Def_FranklKupavskii2022_EMC_IsInitial
import Definitions.Def_FranklKupavskii2022_EMC_trace

open FinsetFamily

namespace FranklKupavskii2022.EMC

/-- Proposition 6 (Frankl–Kupavskii, arXiv:1806.08855v3, p. 4): if `F` is initial and `ν(F) ≤ s`
then `ν(∂F(∅)) ≤ s` (12).

**Formalization Note.** As in Lemma 5 (the preceding statement on the page), `F ⊂ \binom{[n]}{k}`.
The Sect. 1 standing assumption "positive integers n, k, s satisfy n ≥ k(s + 1)" is kept as
`1 ≤ k`, `1 ≤ s`, `k * (s + 1) ≤ n`. -/
theorem trace_empty_shadow_matching (n k s : ℕ) (hk : 1 ≤ k) (hs : 1 ≤ s) (hn : k * (s + 1) ≤ n)
    (F : Finset (Finset ℕ)) (hF : F ⊆ (Finset.Icc 1 n).powersetCard k) (hinit : IsInitial n k F)
    (hν : matchingNumber F ≤ s) :
    matchingNumber (∂ (trace s F ∅)) ≤ s := by sorry

end FranklKupavskii2022.EMC
