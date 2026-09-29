import Mathlib

namespace ChvatalPolytopes.Separation

/-- **Proposition 2.1** (Chvátal 1975, pp. 139–140). Let `S` be a finite set of solutions
`x = (x_u : u ∈ V)` of the system (2.1)
`−x_u ≤ 0 (u ∈ V)`, `Σ (a_{iu} x_u : u ∈ V) ≤ b_i (i ∈ J)`.
Then the set of all solutions of (2.1) is the convex hull of `S` if and only if, for every
integer-valued vector `c = (c_u : u ∈ V)`,
`max {cx : x ∈ S} = min {Σ (λ_i b_i : i ∈ J) : λ_i ≥ 0 for all i ∈ J and
Σ (λ_i a_{iu} : i ∈ J) ≥ c_u for all u ∈ V}`.

"min = max" is stated as: (a) every feasible `λ` has objective `≥ max_{x ∈ S} cx`, and (b) some
feasible `λ` has objective equal to it. The hypothesis `S.Nonempty` is added (the paper's
`max {cx : x ∈ S}` requires it). The nonnegativity rows `−x_u ≤ 0` are kept as the conjunct
`∀ u, 0 ≤ x u`; `J` is a finite index type and the coefficients `a`, `b` are real. -/
theorem convexHull_iff_minmax {V : Type*} [Fintype V] {J : Type*} [Fintype J]
    (a : J → V → ℝ) (b : J → ℝ) (S : Finset (V → ℝ)) (hS : S.Nonempty)
    (hSsol : ∀ x ∈ S, (∀ u, 0 ≤ x u) ∧ ∀ i, ∑ u, a i u * x u ≤ b i) :
    {x : V → ℝ | (∀ u, 0 ≤ x u) ∧ ∀ i, ∑ u, a i u * x u ≤ b i} = convexHull ℝ (S : Set (V → ℝ)) ↔
      ∀ c : V → ℤ,
        (∀ lam : J → ℝ, (∀ i, 0 ≤ lam i) → (∀ u, (c u : ℝ) ≤ ∑ i, lam i * a i u) →
          S.sup' hS (fun x => ∑ u, (c u : ℝ) * x u) ≤ ∑ i, lam i * b i) ∧
        (∃ lam : J → ℝ, (∀ i, 0 ≤ lam i) ∧ (∀ u, (c u : ℝ) ≤ ∑ i, lam i * a i u) ∧
          ∑ i, lam i * b i = S.sup' hS (fun x => ∑ u, (c u : ℝ) * x u)) := by sorry

end ChvatalPolytopes.Separation

