import Mathlib
import Definitions.Def_ProcessingNetworks_BackPressure_SPNPlanningData

namespace ProcessingNetworks.BackPressure

/-- Assumption 9.1, Dai & Harrison p. 164 (PDF p. 180): each column of the input-output matrix
`R` contains exactly one positive element. -/
def SatisfiesAssumption91 {I J K : ℕ} (dat : SPNPlanningData I J K) : Prop :=
  ∀ j : Fin J, ∃! i : Fin I, 0 < dat.R i j

/-- `i(j)`, the unique buffer served by activity `j` under Assumption 9.1. -/
noncomputable def servesBuffer {I J K : ℕ} {dat : SPNPlanningData I J K}
    (h91 : SatisfiesAssumption91 dat) (j : Fin J) : Fin I :=
  (h91 j).choose

/-- Assumption 9.2, Dai & Harrison p. 164 (PDF p. 180): there exists a vector `x ≥ 0` such that
`Rx > 0` (componentwise). -/
def SatisfiesAssumption92 {I J K : ℕ} (dat : SPNPlanningData I J K) : Prop :=
  ∃ x : Fin J → ℝ, (∀ j, 0 ≤ x j) ∧ ∀ i : Fin I, 0 < (dat.R.mulVec x) i

/-- Definition 9.5 (Leontief network), Dai & Harrison p. 167 (PDF p. 183): an SPN whose data
satisfy both Assumption 9.1 and Assumption 9.2. -/
def IsLeontiefNetwork {I J K : ℕ} (dat : SPNPlanningData I J K) : Prop :=
  SatisfiesAssumption91 dat ∧ SatisfiesAssumption92 dat

/-- A **basis** (Dai & Harrison p. 165, PDF p. 181): a choice of `I` activities among the `J ≥ I`
available, one serving each buffer. `choice i` is the basic activity assigned to buffer `i`;
`serves` records that it genuinely serves buffer `i` (i.e. `R i (choice i) > 0`), consistent with
Assumption 9.1's `i(j)` map. Named `ActivityBasis`, not `Basis`, to avoid colliding with Mathlib's
vector-space `Basis` type — this is a narrower, SPN-specific notion. -/
structure ActivityBasis {I J K : ℕ} (dat : SPNPlanningData I J K) where
  choice : Fin I → Fin J
  injective : Function.Injective choice
  serves : ∀ i, 0 < dat.R i (choice i)

/-- The basis matrix `R̂` (Dai & Harrison p. 165, PDF p. 181): the `I × I` submatrix of `R` formed
from the basic activities' columns. -/
noncomputable def basisMatrix {I J K : ℕ} {dat : SPNPlanningData I J K} (basis : ActivityBasis dat) :
    Matrix (Fin I) (Fin I) ℝ :=
  fun i i' => dat.R i (basis.choice i')

/-- `R̂ = (I - Q)Δ⁻¹` (Eq. 9.3): `Q` is a nonnegative square matrix and `Δ` is diagonal with
positive diagonal elements. -/
def IsBasisDecomposition {I : ℕ} (Rhat Q : Matrix (Fin I) (Fin I) ℝ) (Δ : Fin I → ℝ) : Prop :=
  (∀ i, 0 < Δ i) ∧ (∀ i i', 0 ≤ Q i i') ∧ Rhat = (1 - Q) * Matrix.diagonal (fun i => (Δ i)⁻¹)

end ProcessingNetworks.BackPressure
