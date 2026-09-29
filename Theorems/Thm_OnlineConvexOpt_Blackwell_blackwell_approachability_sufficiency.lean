import Mathlib
import Definitions.Def_OnlineConvexOpt_Blackwell_Approachability

namespace OnlineConvexOpt.Blackwell

/-- Theorem 13.4, Blackwell's Approachability Theorem — **sufficiency direction only** (Hazan,
*Introduction to Online Convex Optimization*, 2nd ed., arXiv:1909.05207v3, p. 209, PDF p. 231).
For any vector game `K1, K2, u` with both players' decision sets nonempty, if
`∀y∈K2, ∃x∈K1, u(x,y)∈S`, then the closed, bounded, convex set `S` is approachable.

The book's own theorem is a biconditional ("the closed, bounded and convex set `S` is
approachable if and only if..."), but states explicitly: "The necessity of this condition is
left as an exercise, and the more interesting implication is that any set that satisfies this
condition is, in fact, approachable. Our reductions henceforth give an explicit proof of
Blackwell's theorem" — the book proves, and this mission drafts, only the sufficiency direction
(the `↔`'s `←`), per `CAPTAIN_BRIEF.md` rule 6 (a result may only be drafted to the extent its
hypotheses/proof are actually pinned down on the page) and `BRIEF.md`'s explicit scope
instruction; see `STATUS.md`. -/
theorem blackwell_approachability_sufficiency
    {E1 E2 F : Type*} [NormedAddCommGroup E1] [NormedSpace ℝ E1] [NormedAddCommGroup E2]
    [NormedSpace ℝ E2] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K1 : Set E1) (K2 : Set E2) (u : E1 → E2 → F) (S : Set F)
    (hSconv : Convex ℝ S) (hSbdd : Bornology.IsBounded S) (hSclosed : IsClosed S)
    (hK1bdd : Bornology.IsBounded K1) (hK1closed : IsClosed K1) (hK1conv : Convex ℝ K1)
    (hK2bdd : Bornology.IsBounded K2) (hK2closed : IsClosed K2) (hK2conv : Convex ℝ K2)
    (hK1ne : K1.Nonempty) (hK2ne : K2.Nonempty)
    (hcond : ∀ y ∈ K2, ∃ x ∈ K1, u x y ∈ S) :
    IsApproachable K1 K2 u S := by sorry

end OnlineConvexOpt.Blackwell
