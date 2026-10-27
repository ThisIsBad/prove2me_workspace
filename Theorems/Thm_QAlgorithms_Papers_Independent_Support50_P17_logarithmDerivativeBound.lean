import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P17

noncomputable section

open MeasureTheory

open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Support50.P17

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the exact frozen support predicate and signed, unnormalised entropy.

open QAlgorithms.Papers.Independent.Dependency50.P21 (IsSupported relativeEntropy)

/-- PDF pp.6–7, Lemma 3, (14): actual logarithmic-derivative operator bound.
Convergence of each resolvent entry is concluded, not inserted as an extra hypothesis.
Loewner order is positivity of the difference; gamma=t=0 uses the valid value 0/0=0. -/
theorem logarithmDerivativeBound {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (a b : Matrix I I ℂ) (ha : a.PosDef) (hb : b.PosDef)
    (htrace : a.trace = b.trace) (gamma : ℝ) (hgamma : 0 ≤ gamma)
    (hlower : (a - (gamma : ℂ) • (1 : Matrix I I ℂ)).PosSemidef) :
    let t := traceDistance b a
    (∀ i j : I, IntegrableOn (fun s => resolventIntegrand b (b - a) s i j)
      (Set.Ioi (0 : ℝ))) ∧
    (((t / (gamma + t) : ℝ) : ℂ) • (1 : Matrix I I ℂ) -
      logarithmDerivativeMap b (b - a)).PosSemidef := by sorry

end QAlgorithms.Papers.Independent.Support50.P17

end

