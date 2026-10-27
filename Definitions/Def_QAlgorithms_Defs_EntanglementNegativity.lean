import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Entanglement

/-- arxiv-quant-ph-0102117v1 PDF p.1; arxiv-quant-ph-0102117v1 PDF p.2. -/
def negativity {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (X : Matrix (I × J) (I × J) ℂ) : ℝ := (traceNorm (partialTransposeFirst X)-1)/2

/-- Sanity check for the source model (arxiv-quant-ph-0102117v1 PDF p.1). -/
example {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] :
    negativity (0 : Matrix (I × J) (I × J) ℂ) = -(1/2) := by
  have hz : partialTransposeFirst (0 : Matrix (I × J) (I × J) ℂ) = 0 := rfl
  rw [negativity,hz]
  norm_num [traceNorm,cfc_zero]

end QAlgorithms.Entanglement
