import Mathlib
import Definitions.Def_FoundationsML_MultiClass_EmpiricalRademacherComplexity_v2
import Definitions.Def_FoundationsML_MultiClass_MaxFamily


namespace FoundationsML.MultiClass

/-- Lemma 9.1 (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed.,
MIT Press 2018, p. 216, PDF p. 233). Let `F_1,…,F_l` be `l ≥ 1` hypothesis sets in `ℝ^X`
(bounded, as Definition 3.1 requires) and `G = {max{h_1,…,h_l} : h_i ∈ F_i}`. Then, for any
sample `S` of size `m`, the empirical Rademacher complexity of `G` is bounded by
`∑_{j=1}^l R̂_S(F_j)`.

**Formalization Note.** Replaces `max_hypothesis_sets_rademacher_bound`, which used the
retired `EmpiricalRademacherComplexity` whose supremum `⨆ g ∈ G, …` on `ℝ` is clipped at `0`
and returns the junk value `0` for an unbounded family, so an unbounded `F_j` had complexity
`0` while `G` did not (the disproof). The corrected `EmpiricalRademacherComplexity` (`_v2`,
supremum over exactly the family) is used, and Definition 3.1's standing assumption that each
family maps into a bounded interval `[a,b]` is explicit (`hFb`); for an unbounded `F_j` the
book's right-hand side would be `+∞`. The index set `ι` with `[Fintype ι] [Nonempty ι]` is
the book's `[l]`, `l ≥ 1`. -/
theorem max_hypothesis_sets_rademacher_bound_v2
    {X ι : Type*} [Fintype ι] [Nonempty ι] (F : ι → Set (X → ℝ))
    (hFb : ∃ a b : ℝ, ∀ j, ∀ g ∈ F j, ∀ x, g x ∈ Set.Icc a b)
    (m : ℕ) (S : Fin m → X) :
    EmpiricalRademacherComplexity (MaxFamily F) S ≤
      ∑ j, EmpiricalRademacherComplexity (F j) S := by sorry

end FoundationsML.MultiClass

