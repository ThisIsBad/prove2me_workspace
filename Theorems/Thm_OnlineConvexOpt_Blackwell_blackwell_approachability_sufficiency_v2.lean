import Mathlib
import Definitions.Def_OnlineConvexOpt_Blackwell_Approachability



namespace OnlineConvexOpt.Blackwell

/-- Theorem 13.4, Blackwell's Approachability Theorem — **sufficiency direction only** (Hazan,
*Introduction to Online Convex Optimization*, 2nd ed., arXiv:1909.05207v3, p. 209, PDF p. 231).
For a generalized vector game `K1, K2, u` (Definition 13.2: `K1`, `K2` nonempty, bounded,
convex and closed — here compact — decision sets; `u` a vector payoff with values in `ℝ^d`,
biaffine and jointly continuous on `K1 × K2`, as for the mixed extension of Definition 13.1's
finite games, `u(x,y) = E_{i∼x,j∼y}[u(i,j)]`), if `∀y∈K2, ∃x∈K1, u(x,y)∈S`, then the closed,
bounded, convex set `S ⊆ ℝ^d` is approachable (Definition 13.3). The book's theorem is a
biconditional; it proves, and this statement drafts, only the sufficiency direction.

Corrected version: the retired statement took an arbitrary payoff map `u : E1 → E2 → F` on
arbitrary normed spaces, for which the theorem is false (a discontinuous `u` lets the adversary
out-guess every non-anticipating strategy). The proof's minimax step (Lemma 13.6, Sion's
theorem applied to `w^⊤u(x,y)`) needs `u` convex-concave and continuous on compact convex sets,
and the OCO step (Theorem 13.7 with online gradient descent on the unit ball of `ℝ^d`) needs
the payoffs bounded and the payoff space Euclidean; these unwritten standing assumptions of
Definition 13.2 are now explicit. -/
theorem blackwell_approachability_sufficiency_v2
    {E1 E2 : Type*} [NormedAddCommGroup E1] [NormedSpace ℝ E1] [NormedAddCommGroup E2]
    [NormedSpace ℝ E2] {d : ℕ}
    (K1 : Set E1) (K2 : Set E2) (u : E1 → E2 → EuclideanSpace ℝ (Fin d))
    (S : Set (EuclideanSpace ℝ (Fin d)))
    (hSconv : Convex ℝ S) (hSbdd : Bornology.IsBounded S) (hSclosed : IsClosed S)
    (hK1cpt : IsCompact K1) (hK1conv : Convex ℝ K1) (hK1ne : K1.Nonempty)
    (hK2cpt : IsCompact K2) (hK2conv : Convex ℝ K2) (hK2ne : K2.Nonempty)
    (hucont : ContinuousOn (fun p : E1 × E2 => u p.1 p.2) (K1 ×ˢ K2))
    (huaffx : ∀ y ∈ K2, ∀ x₁ ∈ K1, ∀ x₂ ∈ K1, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      u (a • x₁ + b • x₂) y = a • u x₁ y + b • u x₂ y)
    (huaffy : ∀ x ∈ K1, ∀ y₁ ∈ K2, ∀ y₂ ∈ K2, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      u x (a • y₁ + b • y₂) = a • u x y₁ + b • u x y₂)
    (hcond : ∀ y ∈ K2, ∃ x ∈ K1, u x y ∈ S) :
    IsApproachable K1 K2 u S := by sorry

end OnlineConvexOpt.Blackwell

