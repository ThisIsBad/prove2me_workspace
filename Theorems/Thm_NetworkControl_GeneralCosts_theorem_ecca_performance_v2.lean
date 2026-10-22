import Mathlib
import Definitions.Def_NetworkControl_GeneralCosts_eccaAdmitted
import Definitions.Def_NetworkControl_GeneralCosts_virtualPowerQueue


namespace NetworkControl.GeneralCosts

/-- Theorem 6.3 (ECCA Performance), Georgiadis–Neely–Tassiulas pp. 115–117. For any topology
state process `S(t)` and any input process `A(t)` with `0 ≤ A_i(t) ≤ R̂`, the Energy Constrained
Control Algorithm — flow control `R_i(t) = eccaAdmitted (U_i(t)) V (A_i(t))`, power allocation
`P(t)` maximizing `Σ_i [U_i(t) C_i(P, S(t)) - D(t) P_i]` over `P ≥ 0`, `Σ_i P_i ≤ Pmax`, and the
virtual power queue `D(t)` of (6.13) — guarantees `U_i(t) ≤ V + R̂` for all `i, t`,
`D(t) ≤ βV + βR̂ + Pmax` for all `t`, and hence a total energy of at most `Pav·T + Dmax` over any
`T`-slot window. `hCbeta` is the `β`-condition `C_i(P,S) ≤ C_i(P^{[i]},S) + βP_i` of p. 117.

Corrected version: the transmission-rate functions are nonnegative, `C_i(P, S) ≥ 0`, as
everywhere in the monograph (the queueing law `max[U - C, 0] + R` presupposes it); the retired
version omitted this standing assumption, so a negative "rate" let the backlog grow without
bound. -/
theorem theorem_ecca_performance_v2
    {L : ℕ} {Chan : Type*}
    (V Rhat Pmax Pav β : ℝ) (hV : 0 ≤ V) (hRhat : 0 ≤ Rhat) (hPmax : 0 < Pmax)
    (hPav : 0 < Pav) (hPavLtPmax : Pav < Pmax) (hβ : 0 < β)
    (A : ℕ → Fin L → ℝ) (hA0 : ∀ t i, 0 ≤ A t i) (hAle : ∀ t i, A t i ≤ Rhat)
    (S : ℕ → Chan)
    (C : (Fin L → ℝ) → Chan → Fin L → ℝ)
    (hCnonneg : ∀ (P : Fin L → ℝ) (s : Chan) (i : Fin L), 0 ≤ C P s i)
    (hCbeta : ∀ (P : Fin L → ℝ) (s : Chan) (i : Fin L), (∀ j, 0 ≤ P j) →
      (∑ j : Fin L, P j) ≤ Pmax → C P s i ≤ C (Function.update P i 0) s i + β * P i)
    (U : ℕ → Fin L → ℝ) (hU0 : ∀ i : Fin L, U 0 i = 0)
    (P : ℕ → Fin L → ℝ) (hPnonneg : ∀ t : ℕ, ∀ i : Fin L, 0 ≤ P t i)
    (hPbudget : ∀ t : ℕ, (∑ i : Fin L, P t i) ≤ Pmax)
    (D : ℕ → ℝ) (hDeq : ∀ t : ℕ, D t = virtualPowerQueue P Pav t)
    (hPopt : ∀ t : ℕ, ∀ P' : Fin L → ℝ, (∀ i : Fin L, 0 ≤ P' i) → (∑ i : Fin L, P' i) ≤ Pmax →
      (∑ i : Fin L, (U t i * C P' (S t) i - D t * P' i))
        ≤ ∑ i : Fin L, (U t i * C (P t) (S t) i - D t * (P t) i))
    (hUrec : ∀ t : ℕ, ∀ i : Fin L,
      U (t + 1) i = max (U t i - C (P t) (S t) i) 0 + eccaAdmitted (U t i) V (A t i)) :
    (∀ t : ℕ, ∀ i : Fin L, U t i ≤ V + Rhat) ∧
      (∀ t : ℕ, D t ≤ β * V + β * Rhat + Pmax) ∧
      (∀ t0 T : ℕ, (∑ τ ∈ Finset.range T, ∑ i : Fin L, P (t0 + τ) i)
        ≤ Pav * (T : ℝ) + (β * V + β * Rhat + Pmax)) := by sorry

end NetworkControl.GeneralCosts

