import Mathlib
import Definitions.Def_FranklKupavskii2022_EMC_matchingNumber
import Definitions.Def_FranklKupavskii2022_EMC_IsInitial
import Definitions.Def_FranklKupavskii2022_EMC_trace

open FinsetFamily

namespace FranklKupavskii2022.EMC

/-- Lemma 5 (Frankl–Kupavskii, arXiv:1806.08855v3, p. 4, citing Frankl 2013 [15]): if
`F ⊂ \binom{[n]}{k}` is initial and `ν(F) ≤ s`, then `s|∂F(∅)| ≥ |F(∅)|` (11).

**Formalization Note.** `F(∅) = trace s F ∅` (the members of `F` disjoint from `[s+1]`), and
`∂F(∅)` is its shadow. The Sect. 1 standing assumption (p. 1) "positive integers n, k, s satisfy
n ≥ k(s + 1)" is kept as `1 ≤ k`, `1 ≤ s`, `k * (s + 1) ≤ n`; at `k = 0`, `F = {∅}` would give
`0 ≥ 1`. -/
theorem trace_empty_shadow_bound (n k s : ℕ) (hk : 1 ≤ k) (hs : 1 ≤ s) (hn : k * (s + 1) ≤ n)
    (F : Finset (Finset ℕ)) (hF : F ⊆ (Finset.Icc 1 n).powersetCard k) (hinit : IsInitial n k F)
    (hν : matchingNumber F ≤ s) :
    (trace s F ∅).card ≤ s * (∂ (trace s F ∅)).card := by sorry

end FranklKupavskii2022.EMC
