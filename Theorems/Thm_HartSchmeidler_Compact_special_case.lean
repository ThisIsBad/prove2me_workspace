import Definitions.Def_HartSchmeidler_Compact_Game

namespace HartSchmeidler.Compact

open MeasureTheory

/-- Proof of Theorem 3, pp. 24–25, the special case: let `p` be a regular probability measure
on `S` that is a cluster point, against continuous functions, of the correlated equilibria
`q_T` of the f-set games `Γ_T` (`T` ranging over the f-sets containing a fixed profile `ŝ`).
Then (4) holds for every deviation `ζⁱ` with `ζⁱ = tⁱ` on a Borel set `Rⁱ` and the identity
elsewhere. -/
theorem special_case {ι : Type*} [Nonempty ι] [DecidableEq ι] {S : ι → Type*}
    [∀ i, TopologicalSpace (S i)] [∀ i, CompactSpace (S i)] [∀ i, T2Space (S i)]
    [∀ i, Nonempty (S i)] [∀ i, MeasurableSpace (S i)] [∀ i, BorelSpace (S i)]
    (h : ι → Profile S → ℝ) (hcont : ∀ i, Continuous (h i))
    (ŝ : Profile S)
    (F : (∀ i, Finset (S i)) → Finset (Profile S)) (w : (∀ i, Finset (S i)) → Profile S → ℝ)
    (hFw : ∀ T, IsAnchoredFSet ŝ T → IsFSetCE h T (F T) (w T))
    (p : Measure (Profile S)) [IsProbabilityMeasure p] (hp : p.Regular)
    (hclus : ∀ (f : C(Profile S, ℝ)) (ε : ℝ), 0 < ε →
      ∀ T₀, IsAnchoredFSet ŝ T₀ → ∃ T, IsAnchoredFSet ŝ T ∧ (∀ i, T₀ i ⊆ T i) ∧
        |∫ s, f s ∂p - ∑ s ∈ F T, w T s * f s| < ε)
    (i : ι) (t : S i) (R : Set (S i)) (hR : MeasurableSet R) :
    Integrable
        (fun s : Profile S => h i s - h i (Function.update s i (specialDeviation t R (s i)))) p ∧
      0 ≤ ∫ s : Profile S, (h i s - h i (Function.update s i (specialDeviation t R (s i)))) ∂p := by sorry

end HartSchmeidler.Compact

