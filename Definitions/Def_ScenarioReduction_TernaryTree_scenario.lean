import Mathlib

namespace ScenarioReduction.TernaryTree

/-- Regular ternary scenario tree, eq. (19) of Heitsch–Römisch (2003), with `d = 3`.
A scenario is indexed by `σ : Fin K → Fin 3`, where `σ r` is the branch taken at paper level
`r + 1`; the `Fin 3` values `0, 1, 2` stand for the paper's indices `i = 1, 2, 3`, i.e. for the
increments `-δ^{r+1}, 0, +δ^{r+1}`. The scenario is the vector `(ω⁰, …, ωᴷ) ∈ ℝ^{K+1}` with
`ωᵏ = Σ_{j=1}^{k} (i_j - 2) δ^j`; level `0` is the empty sum (the common root, `δ⁰ = 0`). -/
noncomputable def scenario {K : ℕ} (δ : ℕ → ℝ) (σ : Fin K → Fin 3) : Fin (K + 1) → ℝ :=
  fun k => ∑ r ∈ Finset.univ.filter (fun r : Fin K => r.val < k.val),
    (((σ r : ℕ) : ℝ) - 1) * δ (r.val + 1)

end ScenarioReduction.TernaryTree
