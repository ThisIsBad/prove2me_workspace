import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_BaselineAssumptions
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation

namespace ProcessingNetworks.Stability

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Proposition 3.9 (reachability of the empty state), Dai & Harrison, p. 61: assume the empty
state `x*` (`hxstar`) is unique among states mapping to `(0,0)` under `f`, and (Remark 3.3, a
consequence of the Chapter 2 model that the proof uses) that no service is open while all buffers
are empty: `Z(t) = 0 → N(t) = 0`. Under Eq. (3.18) — for every state `x` there is a time `t > 0`
with `P_x(Z(t) = 0 ∣ τ > t) > 0`, where `τ` is the time of the first external arrival, so that
`{τ > t}` is the event `E(t) = E(0)` of no external arrival in `(0, t]` — and the baseline
stochastic assumptions, `x*` is reachable from every state `x`: there is a time `t > 0` with
`P_x(X(t) = x*) > 0`. `P_x` is `ℙ[|{X(0) = x}]`; every state is given positive initial mass by
`hsupp`, so that these conditional laws are all defined. -/
theorem empty_state_reachable {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω]
    {I J : ℕ} {N0 : Fin J → ℕ} {N : ℝ → Ω → Fin J → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    {E : Fin I → ℝ → Ω → ℕ} {lam : Fin I → ℝ≥0}
    {v : Fin J → ℕ → Ω → ℝ} {φ : Fin J → ℕ → Ω → Fin I → ℕ}
    {m : Fin J → ℝ} {Γ : Fin J → Fin I → ℝ} {Psi : Fin J → ℕ → Ω → ℝ × (Fin I → ℕ)}
    (hbase : BaselineAssumptions I J N0 E lam v φ m Γ Psi)
    (M : MarkovRepresentation Xstate I J N Z)
    (hsupp : ∀ x : Xstate, ℙ {ω | M.X 0 ω = x} ≠ 0)
    (hZN : ∀ (t : ℝ) (ω : Ω), Z t ω = 0 → N t ω = 0)
    (xstar : Xstate) (hxstar : M.f xstar = (0, 0))
    (hxstar_unique : ∀ x, M.f x = (0, 0) → x = xstar)
    (h318 : ∀ x : Xstate, ∃ t : ℝ, 0 < t ∧
      (ℙ[|{ω | M.X 0 ω = x}])[|{ω | ∀ i, E i t ω = E i 0 ω}] {ω | Z t ω = 0} > 0) :
    ∀ x : Xstate, ∃ t : ℝ, 0 < t ∧ (ℙ[|{ω | M.X 0 ω = x}]) {ω | M.X t ω = xstar} > 0 := by sorry

end ProcessingNetworks.Stability
