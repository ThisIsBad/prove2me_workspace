import Mathlib
import Definitions.Def_BertsekasShreve_ImperfectInfo_SufficientStatistic

open MeasureTheory ProbabilityTheory

namespace BertsekasShreve.ImperfectInfo

/-- Lemma 10.1 (p. 253). -/
theorem lemma_10_1 {S C Z : Type}
    [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
    [TopologicalSpace C] [MeasurableSpace C] [BorelSpace C]
    [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (M : ISIModel S C Z) {Y : ℕ → Type} [∀ k, TopologicalSpace (Y k)] [∀ k, MeasurableSpace (Y k)]
    (σ : SuffStat M Y)
    (p : ProbabilityMeasure S) (μ : (k : ℕ) → Y k → ProbabilityMeasure C)
    (hμ : σ.IsMarkovPolicy μ) (k : ℕ) (hk : k < M.N) (B : Set (Hist Y C k))
    (hB : MeasurableSet B) :
    M.law (σ.toISI μ) p k (σ.V p k ⁻¹' B) = σ.lawHat (markovToPolicy μ) (σ.phi p) k B := by sorry

end BertsekasShreve.ImperfectInfo

