import Mathlib
import Definitions.Def_NelderMeadLD_Conv1D_Algorithm

namespace NelderMeadLD.Rate1D

open Classical
open NelderMeadLD.Conv1D

/-! The one-dimensional Algorithm NM (`ParamsOK`, `xr`, `xe`, `xc`, `xcc`, `Move`, `move`,
`place`, `step`, `run`, `IsStart`, `diam`, `Bracketed`) is the shared module
`NelderMeadLD.Conv1D.Algorithm`. The state is the ordered pair `p = (x₁, x₂)`: `p.1` is the
best vertex `x₁` and `p.2` the worst vertex `x₂`.

### Objects of §4.3 (reflection coefficient `ρ = 1`) -/

/-- The type of iteration `k` of the run with `ρ = 1`. -/
noncomputable def moveAt (f : ℝ → ℝ) (χ γ σ : ℝ) (p0 : ℝ × ℝ) (k : ℕ) : Move :=
  move f 1 χ γ (run f 1 χ γ σ p0 k)

/-- A contraction is an outside or an inside contraction (a shrink is not a contraction). -/
def IsContraction (m : Move) : Prop :=
  m = Move.outside ∨ m = Move.inside

/-- `r* = ⌈χ − 1⌉` of Lemma 4.6, as a natural number (equal to the paper's value for `χ > 1`). -/
noncomputable def rStar (χ : ℝ) : ℕ := ⌈χ - 1⌉₊

/-- `N_NM = max(χ, 1/γ)` of Lemma 4.7 (the constant (4.3) with `ρ = 1`). -/
noncomputable def NNM1 (χ γ : ℝ) : ℝ := max χ (1 / γ)

/-- `j*` of Lemma 4.7: the largest `j ≤ ⌈N_NM⌉` with `χ + χ² + ⋯ + χ^j < N_NM`
(`j = 0` has the empty sum `0`). -/
noncomputable def jStar (χ γ : ℝ) : ℕ :=
  Nat.findGreatest (fun j => ∑ i ∈ Finset.range j, χ ^ (i + 1) < NNM1 χ γ) ⌈NNM1 χ γ⌉₊

/-- `K` is the iteration index of Lemma 4.2 for `ρ = 1`: the first iteration at which the
up–down–up relation (4.2), `f₂^{(K)} ≥ f₁^{(K)}` and `f₁^{(K)} ≤ f_e^{(K)}`, holds. -/
def FirstBracket (f : ℝ → ℝ) (χ γ σ : ℝ) (p0 : ℝ × ℝ) (K : ℕ) : Prop :=
  Bracketed 1 χ f (run f 1 χ γ σ p0 K) ∧ ∀ j < K, ¬ Bracketed 1 χ f (run f 1 χ γ σ p0 j)

end NelderMeadLD.Rate1D
