import Mathlib

open scoped InnerProductSpace

namespace SPOBounds.Natarajan

/-- `w` is an optimization oracle for the feasible region `S` (arXiv:1905.11488v3, p. 5):
for every cost vector `c`, `w c` is a minimizer of `v ↦ ⟪c, v⟫` over `S`. No tie-breaking rule
is imposed. -/
def IsOracle {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))
    (w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ c : EuclideanSpace ℝ (Fin d), w c ∈ S ∧ ∀ v ∈ S, ⟪c, w c⟫_ℝ ≤ ⟪c, v⟫_ℝ

/-- `S` is a polyhedron: the solution set of finitely many linear inequalities
`⟪a k, v⟫ ≤ b k`, `k = 0, …, m - 1` (p. 10, §3). -/
def IsPolyhedron {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∃ (m : ℕ) (a : Fin m → EuclideanSpace ℝ (Fin d)) (b : Fin m → ℝ),
    S = {v | ∀ k, ⟪a k, v⟫_ℝ ≤ b k}

/-- The SPO loss `ℓ_SPO(ĉ, c) = cᵀ w*(ĉ) − cᵀ w*(c)` of the oracle `w` (p. 6). -/
noncomputable def spoLoss {d : ℕ} (w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (chat c : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ⟪c, w chat⟫_ℝ - ⟪c, w c⟫_ℝ

/-- The linear optimization gap `ω_S(c) = max_{w ∈ S} cᵀw − min_{w ∈ S} cᵀw` (p. 8). -/
noncomputable def linGap {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d)) : ℝ :=
  sSup ((fun v => ⟪c, v⟫_ℝ) '' S) - sInf ((fun v => ⟪c, v⟫_ℝ) '' S)

/-- `ω_S(𝒞) = sup_{c ∈ 𝒞} ω_S(c)` (p. 8). Used only for nonempty bounded `C`. -/
noncomputable def linGapSet {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))
    (C : Set (EuclideanSpace ℝ (Fin d))) : ℝ :=
  sSup (linGap S '' C)

end SPOBounds.Natarajan
