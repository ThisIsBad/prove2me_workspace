import Mathlib

namespace HighDimStat.RandomMatrices

/-- The **elementwise max-norm** `‖M‖_max := max_{i,j} |M_{ij}|`, Wainwright, *High-Dimensional
Statistics* (2019), used in Eq. (6.54)'s hypothesis `‖Σ̂-Σ‖_max ≤ λn`. Realized as `⨆` over the
finite type `Fin d × Fin d`; equals the true maximum for `d > 0`, and is Mathlib's junk value `0`
at `d = 0`, harmless since no entries exist to measure either. -/
noncomputable def maxNorm {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ⨆ p : Fin d × Fin d, |M p.1 p.2|

end HighDimStat.RandomMatrices
