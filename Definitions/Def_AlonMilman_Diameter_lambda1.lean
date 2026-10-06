import Mathlib

namespace AlonMilman.Diameter

/-- `λ₁(G)`: the second-smallest eigenvalue, counted with multiplicity, of the Laplacian
`Q = diag(d(v)) − A_G` (`G.lapMatrix ℝ`) of a finite simple graph `G`.
Mathlib's `eigenvalues₀` lists the eigenvalues in decreasing order, so index `card V - 1` is the
smallest eigenvalue `λ₀` and index `card V - 2` is `λ₁`. For graphs with fewer than two vertices
`λ₁` does not exist and the value is `0` by convention. -/
noncomputable def lambda1 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  if h : 2 ≤ Fintype.card V then
    (G.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩
  else 0

end AlonMilman.Diameter
