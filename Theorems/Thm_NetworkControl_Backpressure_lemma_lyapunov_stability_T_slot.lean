import Mathlib
import Definitions.Def_NetworkControl_Backpressure_StronglyStable
import Definitions.Def_NetworkControl_Backpressure_lyapunovL

namespace NetworkControl.Backpressure

open MeasureTheory

/-- Lemma 4.2 (T-slot Lyapunov drift), p. 52. If there is a positive integer `T` such that
`E{U(τ)} < ∞` for `τ ∈ {0,…,T-1}`, and if there are positive `B, ε` such that at every timeslot
`t0` the conditional expected `T`-slot drift of `L(U(t))` given `U(t0)` satisfies
`E{L(U(t0+T)) - L(U(t0)) | U(t0)} ≤ B - ε Σ_i U_i(t0)`, then the network is strongly stable and
`limsup_{t→∞} (1/t) Σ_τ Σ_i E{U_i(τ)} ≤ B/ε` — the same conclusion as Lemma 4.1, with the drift
measured over a `T`-slot block instead of one.

**Formalization note.** `hIntegInit` is the book's own literal initial-segment hypothesis
(`E{U(τ)}<∞` for `τ<T`); `hIntegU` is an additional guard (not itself in the book's statement)
needed so `∫ ω, U t ω i ∂P` is non-junk at every `t`, matching the pattern used throughout this
series (`03-capacity-region`'s `Integrable` guards, Faithfulness trap 2). The `limsup` conclusion
is stated in the same quantifier-light form as Lemma 4.1. -/
theorem lemma_lyapunov_stability_T_slot
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {L : ℕ} (U : ℕ → Ω → Fin L → ℝ) (T : ℕ) (hT : 0 < T) (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε)
    (hIntegInit : ∀ τ : ℕ, τ < T → ∀ i : Fin L, Integrable (fun ω => U τ ω i) P)
    (hMeas : ∀ t : ℕ, ∀ i : Fin L, Measurable (fun ω => U t ω i))
    (hIntegU : ∀ t : ℕ, ∀ i : Fin L, Integrable (fun ω => U t ω i) P)
    (hIntegDrift : ∀ t0 : ℕ,
      Integrable (fun ω => lyapunovL (U (t0 + T) ω) - lyapunovL (U t0 ω)) P)
    (hdrift : ∀ t0 : ℕ,
      (P[(fun ω => lyapunovL (U (t0 + T) ω) - lyapunovL (U t0 ω))
          | MeasurableSpace.comap (U t0) inferInstance])
        ≤ᵐ[P] (fun ω => B - ε * ∑ i : Fin L, U t0 ω i)) :
    NetworkStronglyStable (fun i t => ∫ ω, U t ω i ∂P) ∧
      ∀ t : ℕ, (1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∑ i : Fin L, ∫ ω, U τ ω i ∂P ≤ B / ε := by sorry

end NetworkControl.Backpressure
