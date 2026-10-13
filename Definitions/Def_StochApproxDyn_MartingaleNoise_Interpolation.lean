import Mathlib
import Definitions.Def_StochApproxDyn_Interpolation_Scheme

namespace StochApproxDyn.MartingaleNoise

open Filter Topology

/-- Standing assumptions on the step sizes (Benaïm 1999, §4.1, p. 11): `{γ_n}_{n ≥ 1}` is a
sequence of nonnegative numbers with `∑_k γ_k = ∞` and `γ_n → 0`. The paper indexes `γ` from
`1`; the value `γ 0` is never used (the limit `γ_n → 0` does not see it). -/
def IsStepSequence (γ : ℕ → ℝ) : Prop :=
  (∀ n : ℕ, 0 ≤ γ (n + 1)) ∧
  Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, γ (i + 1)) atTop atTop ∧
  Tendsto γ atTop (𝓝 0)

/-- The "inverse" of `n ↦ τ_n`, Eq. (8): `m(t) = sup {k ≥ 0 : t ≥ τ_k}`. Under
`IsStepSequence γ` and `t ≥ 0` the set is nonempty (it contains `0`) and bounded (since
`τ_k → ∞`), so `m(t)` is its largest element; `ℕ`'s `sSup` returns `0` on an empty or
unbounded set, which never happens under the standing assumptions. -/
noncomputable def stepIndex (γ : ℕ → ℝ) (t : ℝ) : ℕ :=
  sSup {k : ℕ | StochApproxDyn.Interpolation.tau γ k ≤ t}

/-- The piecewise constant noise process `Ū(τ_n + s) = U_{n+1}` for `0 ≤ s < γ_{n+1}`
(§4.1, p. 12), i.e. `Ū(t) = U_{m(t)+1}` for `t ≥ 0`. Only `t ≥ 0` is meaningful. -/
noncomputable def noisePath {E : Type*} (γ : ℕ → ℝ) (U : ℕ → E) (t : ℝ) : E :=
  U (stepIndex γ t + 1)

/-- The piecewise constant step-size process `γ̄(τ_n + s) = γ_{n+1}` for `0 ≤ s < γ_{n+1}`
(§4.1, p. 12), i.e. `γ̄(t) = γ_{m(t)+1}` for `t ≥ 0`. -/
noncomputable def stepPath (γ : ℕ → ℝ) (t : ℝ) : ℝ :=
  γ (stepIndex γ t + 1)

end StochApproxDyn.MartingaleNoise
