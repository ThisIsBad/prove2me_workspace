import Mathlib
import Definitions.Def_NetworkControl_Backpressure_StronglyStable
import Definitions.Def_NetworkControl_Backpressure_lyapunovL


namespace NetworkControl.Backpressure

open MeasureTheory

/-- Lemma 4.1 (Lyapunov Stability), Georgiadis–Neely–Tassiulas p. 50. Let `L(U) = Σ_i U_i²` with
`E L(U(0)) < ∞`. If there are constants `B > 0`, `ε > 0` such that at every slot `t` the
conditional expected drift satisfies `E{L(U(t+1)) - L(U(t)) | U(t)} ≤ B - ε Σ_i U_i(t)`, then
the network is strongly stable and `limsup_{t→∞} (1/t) Σ_{τ<t} Σ_i E U_i(τ) ≤ B/ε`.

Corrected version: the second conclusion is the monograph's `limsup` bound (read in `EReal`,
where `Filter.limsup` never returns a junk value), not the uniform-in-`t` bound of the retired
version, which silently dropped the initial-condition term `E L(U(0))/(εt)` and claimed more than
the lemma asserts. The hypothesis `E L(U(0)) < ∞` and the nonnegativity of backlogs are the
monograph's standing assumptions. -/
theorem lemma_lyapunov_stability_v2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {L : ℕ} (U : ℕ → Ω → Fin L → ℝ) (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε)
    (hUnn : ∀ t ω i, 0 ≤ U t ω i)
    (hMeas : ∀ t : ℕ, ∀ i : Fin L, Measurable (fun ω => U t ω i))
    (hIntegL0 : Integrable (fun ω => lyapunovL (U 0 ω)) P)
    (hIntegU : ∀ t : ℕ, ∀ i : Fin L, Integrable (fun ω => U t ω i) P)
    (hIntegDrift : ∀ t : ℕ, Integrable (fun ω => lyapunovL (U (t + 1) ω) - lyapunovL (U t ω)) P)
    (hdrift : ∀ t : ℕ,
      (P[(fun ω => lyapunovL (U (t + 1) ω) - lyapunovL (U t ω))
          | MeasurableSpace.comap (U t) inferInstance])
        ≤ᵐ[P] (fun ω => B - ε * ∑ i : Fin L, U t ω i)) :
    NetworkStronglyStable (fun i t => ∫ ω, U t ω i ∂P) ∧
      Filter.limsup
        (fun t : ℕ =>
          (((1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∑ i : Fin L, ∫ ω, U τ ω i ∂P : ℝ) : EReal))
        Filter.atTop ≤ ((B / ε : ℝ) : EReal) := by sorry

end NetworkControl.Backpressure

