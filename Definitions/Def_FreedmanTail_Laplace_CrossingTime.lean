import Mathlib
import Definitions.Def_FreedmanTail_Bernstein_PartialSums

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FreedmanTail.Laplace

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- Freedman (1975), Definition (1.7), p. 102: `τ_a` is the least `n` with `S_n ≥ a`, and
`τ_a = ∞` (here `⊤`) if there is no such `n`. -/
noncomputable def tau (a : ℝ) (X : ℕ → Ω → ℝ) (ω : Ω) : WithTop ℕ := by
  classical
  exact if h : ∃ n : ℕ, a ≤ FreedmanTail.Bernstein.S X n ω then ((Nat.find h : ℕ) : WithTop ℕ) else ⊤

/-- Freedman (1975), Definition (1.7), p. 102: `W_a = T_{τ_a} = Σ_{i=1}^{τ_a} V_i`, a
`[0, ∞]`-valued random variable. On `{τ_a = ∞}` it is the whole series `Σ_{i ≥ 1} V_i`,
which may be `+∞`. Each `V_i` enters through `ENNReal.ofReal`; since `V_i ≥ 0` almost surely,
this clamp changes nothing almost surely. -/
noncomputable def W (a : ℝ) (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ) (P : Measure Ω) (ω : Ω) :
    ℝ≥0∞ :=
  ∑' i : ℕ, if 1 ≤ i ∧ ((i : WithTop ℕ) ≤ tau a X ω) then ENNReal.ofReal (FreedmanTail.Bernstein.V ℱ X P i ω) else 0

/-- `exp[−c·w]` for `w ∈ [0, ∞]`, with the value `0` at `w = ∞` (the paper's convention
`exp[−f(λ)·∞] = 0`, `f(λ) > 0`). -/
noncomputable def expNegMul (c : ℝ) (w : ℝ≥0∞) : ℝ :=
  if w = ⊤ then 0 else Real.exp (-(c * w.toReal))

end FreedmanTail.Laplace
