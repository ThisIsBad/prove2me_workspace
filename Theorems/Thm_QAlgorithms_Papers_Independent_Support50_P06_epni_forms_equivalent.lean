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

/-- PDF p.4, (22) iff (23); both directions proved in note [13], p.5.
This equivalence does not assert EPnI. Infinite output entropy satisfies both
sides; input entropies are finite so the comparison thermal state is defined. -/
theorem epni_forms_equivalent (n : ℕ) (hn : 0 < n) (eta : ℝ)
    (heta : 0 ≤ eta) (heta_one : eta ≤ 1) (rhoA rhoB : State (NumberString n))
    (hA : spectralEntropyNats rhoA.coefficients ≠ ⊤)
    (hB : spectralEntropyNats rhoB.coefficients ≠ ⊤) :
    EpniAt eta rhoA.coefficients rhoB.coefficients ↔
      spectralEntropyNats (identicalThermalKernel n
        (eta * entropyParameter n (spectralEntropyNats rhoA.coefficients) +
          (1 - eta) * entropyParameter n (spectralEntropyNats rhoB.coefficients))) ≤
        spectralEntropyNats (mixedOutput n eta rhoA.coefficients rhoB.coefficients) := by sorry

end QAlgorithms.Papers.Independent.Support50.P06

end

