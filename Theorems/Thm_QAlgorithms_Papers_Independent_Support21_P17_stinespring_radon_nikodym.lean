import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P17

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix Kronecker Topology TensorProduct

open Filter

namespace QAlgorithms.Papers.Independent.Support21.P17

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P50 (NoiseSpace completedTensorMap)

open QAlgorithms.Papers.Independent.Next46.P33 (UltraweakTest)

open QAlgorithms.Papers.Independent.Next46.P32 (PositiveKernel)

open QAlgorithms.Papers.Independent.Information100.P50 (M Lin coefficientMap)

/-- Theorem 3.1, PDF pp.7–8: existence, converse, symmetric square-root form, and
strong uniqueness among all commutant operators, with no positivity assumption on Y.
The uniqueness proof's reference to the dilation of S is read as the fixed dilation of T. -/
theorem stinespring_radon_nikodym {A : Type*} [CStarAlgebra A]
    (G H K : SeparableHilbertSpace) (rho : A →⋆ₐ[ℂ] HilbertEndomorphism G) (h_rho : Function.Injective rho)
    (T : A →ₗ[ℂ] HilbertEndomorphism H) (pi : A →⋆ₐ[ℂ] HilbertEndomorphism K) (V : H →L[ℂ] K)
    (hT : IsNormalCP rho T) (h_dilation : ∀ a, T a = compress V (pi a))
    (h_minimal : IsMinimal pi V) (S : A →ₗ[ℂ] HilbertEndomorphism H) (hS : IsNormalCP rho S) :
    CompletelyDominated S T ↔ ∃ F : HilbertEndomorphism K, CommutesWithRepresentation pi F ∧ PositiveContraction F ∧
      (∀ a, S a = compress V ((pi a).comp F) ∧
        S a = compress V ((cfc Real.sqrt F).comp ((pi a).comp (cfc Real.sqrt F)))) ∧
      ∀ Y : HilbertEndomorphism K, CommutesWithRepresentation pi Y → (∀ a, S a = compress V ((pi a).comp Y)) → Y = F := by sorry

end QAlgorithms.Papers.Independent.Support21.P17

end

