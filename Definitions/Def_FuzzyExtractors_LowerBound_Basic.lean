import Mathlib
import Definitions.Def_FuzzyExtractors_Hamming_Basic

namespace FuzzyExtractors.LowerBound

open scoped ENNReal

noncomputable section

open Classical in
/-- K(𝓜, t, S) (Appendix C, p. 40): the largest `K` such that there is an (𝓜, K, t)-code all of
whose `K` points belong to `S`. The empty code qualifies, so the maximum is attained.
K(𝓜, t), the largest size of an (𝓜, K, t)-code, is `K dis t Finset.univ`. -/
def K {M : Type} (dis : M → M → ℕ) (t : ℕ) (S : Finset M) : ℕ :=
  (S.powerset.filter fun C => FuzzyExtractors.Hamming.IsCode dis C t).sup Finset.card

/-- L(𝓜, t, m) = log(min_{|S| = 2^m} K(𝓜, t, S)) (Appendix C, p. 40), for `2^m = N` a natural
number with `N ≤ |𝓜|`: the minimum ranges over all `N`-element subsets `S` of `𝓜`. -/
def L {M : Type} [Fintype M] (dis : M → M → ℕ) (t N : ℕ)
    (hN : N ≤ Fintype.card M) : ℝ :=
  Real.logb 2 ((Finset.univ.powersetCard N).inf'
    (Finset.powersetCard_nonempty.2 (by simpa using hN))
    fun S => (K dis t S : ℝ))

open Classical in
/-- The set T of points `w ∈ S` that can produce the sketch value `v`, i.e. `Pr[SS(w) = v] > 0`
(Appendix C, proof of Lemma C.1, p. 40). -/
def producers {M V : Type} (SS : M → PMF V) (S : Finset M) (v : V) : Finset M :=
  S.filter fun w => v ∈ (SS w).support

end

end FuzzyExtractors.LowerBound
