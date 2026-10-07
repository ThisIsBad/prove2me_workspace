import Mathlib
import Definitions.Def_SmithRegenerative_Equilibrium_EquilibriumProcess

namespace SmithRegenerative.Equilibrium

open MeasureTheory

/-- **The decomposition (3·4·3)** (Smith 1955, §3·4, proof of Theorem 2, p. 15; unnumbered result).
For an equilibrium process `𝓔(𝔷, 𝒜, {tᵢ})`, every boundary condition `z`, every `A ∈ 𝒜` and every
`t ≥ 0`,
`P{x_t ∈ A | z} = P{x_t ∈ A, t₀ > t | z} + ∫₀^t φ_A(t − τ){1 − F(t − τ)} dH_{K_z}(τ)`.

Formalization Note: `1 − F(v)` is `F (Set.Ioi v)`; `H_{K_z}` is `renewalMeasure (K z) F`; the
Stieltjes integral is over the closed interval `[0, t]`. No hypothesis beyond the equilibrium
property (and the certainty of `𝓔`, built into `EquilibriumProcess`) is used. -/
theorem decomposition_3_4_3 {Ω 𝔛 Z : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝔛]
    (E : EquilibriumProcess Ω 𝔛 Z) (z : Z) (A : Set 𝔛) (hA : A ∈ E.𝒜) (t : ℝ) (ht : 0 ≤ t) :
    (E.P z {ω | E.x t ω ∈ A}).toReal =
      (E.P z {ω | E.x t ω ∈ A ∧ t < E.t 0 ω}).toReal +
        ∫ τ in Set.Icc 0 t, E.φ A (t - τ) * (E.F (Set.Ioi (t - τ))).toReal
          ∂(renewalMeasure (E.K z) E.F) := by sorry

end SmithRegenerative.Equilibrium

