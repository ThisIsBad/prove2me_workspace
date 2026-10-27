import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P15

noncomputable section

open scoped BigOperators

open Filter

namespace QAlgorithms.Papers.Independent.Support21.P15

/-- Unnumbered block-diagonal observation, arXiv:math/0307169v1, PDF p.14:
ell_p^n(S_p^m) embeds isometrically into S_p^(nm), with a contractive projection
onto that same range when p≥1. The Schatten size is the accepted all-matrix
trace-of-power formula, not the ambient entrywise matrix norm. -/
theorem schatten_blockDiagonal (p : ℝ) (hp : 0 < p)
    (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    Function.Injective (schattenBlockInclusion n m) ∧
    (∀ x : Fin n → Matrix (Fin m) (Fin m) ℂ,
      QAlgorithms.Papers.Independent.Information100.P50.schattenNorm (ENNReal.ofReal p)
        (schattenBlockInclusion n m x) =
      finiteLpSize p
        (QAlgorithms.Papers.Independent.Information100.P50.schattenNorm (ENNReal.ofReal p)) x) ∧
    (1 ≤ p →
      (schattenBlockProjection n m).comp (schattenBlockProjection n m) =
        schattenBlockProjection n m ∧
      LinearMap.range (schattenBlockProjection n m) =
        LinearMap.range (schattenBlockInclusion n m) ∧
      ∀ x : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ,
        QAlgorithms.Papers.Independent.Information100.P50.schattenNorm (ENNReal.ofReal p)
          (schattenBlockProjection n m x) ≤
        QAlgorithms.Papers.Independent.Information100.P50.schattenNorm (ENNReal.ofReal p) x) := by sorry

end QAlgorithms.Papers.Independent.Support21.P15

end

