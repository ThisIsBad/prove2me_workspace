import Definitions.Def_GeneralCK_finite_law_regional

theorem GeneralCK.ArchiveRegionalBoundary.canonicalOppositeSide : ∀ (k : ℕ) (μ : GeneralCK.InteriorLaw (Fin k)),
    μ.a ≤ μ.b → μ.a + μ.b ≤ 1 → 1 / 2 ≤ μ.b → μ.gap ≤ μ.cost := by sorry
