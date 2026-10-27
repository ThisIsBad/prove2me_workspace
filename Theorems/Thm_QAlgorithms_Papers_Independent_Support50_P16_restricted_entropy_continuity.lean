import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P16

namespace QAlgorithms.Papers.Independent.Support50.P16

noncomputable section

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

local notation "tau" => QAlgorithms.Papers.Independent.Information100.P76.maximallyMixed

local notation "RE" => QAlgorithms.Papers.Independent.Information100.P54.relativeEntanglement

local notation "RER" => QAlgorithms.Papers.Independent.Information100.P54.regularizedEntanglement

local notation "SQ" => QAlgorithms.Papers.Independent.Dependency50.P19.squashed

local notation "CMI" => QAlgorithms.Papers.Independent.Dependency50.P19.conditionalMutual

local notation "MI" => QAlgorithms.Papers.Independent.Dependency50.P19.mutualInformation

local notation "LOCC" => QAlgorithms.Papers.Independent.Information100.P21.FiniteLOCC

local notation "power" => QAlgorithms.Papers.Independent.Dependency50.P42.dimensionedPower

local notation "index" => QAlgorithms.Papers.Independent.Dependency50.P42.copyIndex

-- Accepted matrix coordinates (not P50.Bipartite, which is a vector space).

local notation "Bipartite" => QAlgorithms.Papers.Independent.Dependency50.P50.BipartiteMat

-- Positive outcome counts follow already from a POVM on a nonzero register.

local notation "FiniteMeasurement" => QAlgorithms.Papers.Independent.Information100.P04.Measurement

local notation "relative" =>
  ((fun _ _ rho => RE rho) : ExtendedEntanglementFunctional)

-- Reuse the accepted operational/variational quantity through a typed notation.

local notation "squashed" =>
  ((fun _ _ rho => ENNReal.ofReal (SQ rho)) : ExtendedEntanglementFunctional)

local notation "originalMarginal" => QAlgorithms.Papers.Independent.Information100.P04.principalMarginal

-- Exact accepted partial trace of the same AA'BB' extension.

local notation "ancillaryMarginal" => QAlgorithms.Papers.Independent.Information100.P04.ancillaryMarginal

local notation "distillable" =>
  ((fun _ _ rho => ENNReal.ofReal (QAlgorithms.Papers.Independent.Gap48.P32.twoWayDistillable rho)) : ExtendedEntanglementFunctional)

local notation "cost" =>
  ((fun _ _ rho => ENNReal.ofReal (QAlgorithms.Papers.Independent.Dependency50.P42.alternativeCost
    (fun _ _ X Y => traceNorm (X-Y)) rho)) : ExtendedEntanglementFunctional)

/-- Proposition 3, PDF p.5 (announced p.4); proof pp.10--11.
Star-shaped G may be nonconvex and nonclosed; M may be empty. Finite values
are conclusions, before their toReal difference is used. -/
theorem restricted_entropy_continuity (k : ℕ+)
    (G : Set (Matrix (Fin (k : ℕ)) (Fin (k : ℕ)) ℂ))
    (M : Set (FiniteMeasurement (Fin (k : ℕ))))
    (hstates : ∀ sigma ∈ G, IsDensityMatrix sigma)
    (htau : tau k ∈ G)
    (hstar : ∀ sigma ∈ G, ∀ p : ℝ, 0 ≤ p → p ≤ 1 →
      (p : ℂ) • sigma + ((1-p : ℝ) : ℂ) • tau k ∈ G)
    (rho sigma : Matrix (Fin (k : ℕ)) (Fin (k : ℕ)) ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (epsilon : ℝ) (heps0 : 0 ≤ epsilon)
    (hdistance : measurementDistance M rho sigma ≤ epsilon)
    (heps1 : epsilon ≤ 1 / Real.exp 1) :
    restrictedEntropy G M rho ≠ ⊤ ∧ restrictedEntropy G M sigma ≠ ⊤ ∧
    |(restrictedEntropy G M rho).toReal - (restrictedEntropy G M sigma).toReal| ≤
      continuityModulus k epsilon := by sorry

end

end QAlgorithms.Papers.Independent.Support50.P16

