import Mathlib
import Definitions.Def_KWSpectrum_Estimator_Model

namespace KWSpectrum.Estimator

open QAlgorithms QAlgorithms.Schur

/-- Keyl–Werner, arXiv:quant-ph/0102027v1, §III, p. 3 (highest weight), with weights read as
contents of semistandard fillings (eq. (20)): (i) the Young frame `Y` is a weight of
multiplicity one, i.e. exactly one semistandard filling of `Y` with entries in `{0, …, d − 1}`
has content `(Y₁, …, Y_d)`; (ii) `Y` dominates every weight: for every semistandard filling with
content `μ`, `μ₁ + ⋯ + μ_k ≤ Y₁ + ⋯ + Y_k` for every `k`, with equality of the totals. -/
theorem highest_weight {d N : ℕ} (Y : Partition d N) :
    (∃! T : Y.val.cells → Fin d,
      IsSemistandardFilling Y T ∧ content Y T = fun i => Y.val.rowLen i.val) ∧
    ∀ T : Y.val.cells → Fin d, IsSemistandardFilling Y T →
      (∀ k : ℕ, ∑ i : Fin d with i.val < k, content Y T i ≤
          ∑ i : Fin d with i.val < k, Y.val.rowLen i.val) ∧
      ∑ i : Fin d, content Y T i = ∑ i : Fin d, Y.val.rowLen i.val := by sorry

end KWSpectrum.Estimator

