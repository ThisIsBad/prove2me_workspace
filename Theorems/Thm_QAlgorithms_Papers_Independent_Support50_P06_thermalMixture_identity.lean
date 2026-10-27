import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P06

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P06

open MeasureTheory Filter

open scoped ENNReal BigOperators Topology

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity rankOne)

open QAlgorithms.Papers.Independent.Next46.P32
  (NumberString FockKernel identicalThermalKernel vacuum productCoherentKernel
   jointMix bobMarginal charlieMarginal pureLoss broadcast mixedOutput
   spectralEntropyNats FockPOVM realFockTracePair modeEnergy complexNormal
   StrongConjecture2)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Claimed50.P11 (thermalEntropyInverse)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.4, (18)–(19): the same normalized thermal density is the Gaussian
coherent mixture and the geometric photon-number mixture. Integrability and
probability normalization are conclusions. N=0 uses delta_0, since the printed
Lebesgue density is singular there; the photon representation fixes this limit. -/
theorem thermalMixture_identity (N : ℝ) (hN : 0 ≤ N) :
    IsProbabilityMeasure (complexNormal N 0) ∧
    Integrable (fun alpha : ℂ => alpha) (complexNormal N 0) ∧
    (∫ alpha : ℂ, alpha ∂complexNormal N 0) = 0 ∧
    Integrable (fun alpha : ℂ => Complex.normSq alpha) (complexNormal N 0) ∧
    (∫ alpha : ℂ, Complex.normSq alpha ∂complexNormal N 0) = N ∧
    IsDensity (identicalThermalKernel 1 N) ∧
    coherentMixture N = identicalThermalKernel 1 N ∧
    (∀ a b : NumberString 1,
      Integrable (fun alpha : ℂ => productCoherentKernel 1 (fun _ => alpha) a b)
        (complexNormal N 0) ∧
      identicalThermalKernel 1 N a b = ∑' j : ℕ,
        ((N ^ j / (N + 1) ^ (j + 1) : ℝ) : ℂ) *
          (if a = (fun _ => j) ∧ b = (fun _ => j) then 1 else 0)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P06

end

