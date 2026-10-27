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

/-- PDF p.4, (19)–(20): thermal entropy and the entropy-matched n-mode thermal
products for BOTH independent ports. Matching entropy never identifies an
arbitrary state's physical mean photons with its entropy photon number. -/
theorem thermalEntropy_matching (n : ℕ) (hn : 0 < n) :
    (∀ N : ℝ, 0 ≤ N → spectralEntropyNats (identicalThermalKernel 1 N) =
      ENNReal.ofReal (g N)) ∧
    (∀ rhoA rhoB : State (NumberString n),
      spectralEntropyNats rhoA.coefficients ≠ ⊤ →
      spectralEntropyNats rhoB.coefficients ≠ ⊤ →
      spectralEntropyNats (identicalThermalKernel n
        (entropyParameter n (spectralEntropyNats rhoA.coefficients))) =
          spectralEntropyNats rhoA.coefficients ∧
      spectralEntropyNats (identicalThermalKernel n
        (entropyParameter n (spectralEntropyNats rhoB.coefficients))) =
          spectralEntropyNats rhoB.coefficients) := by sorry

end QAlgorithms.Papers.Independent.Support50.P06

end

