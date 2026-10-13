import Mathlib
import Definitions.Def_RossQC_Regions_Model

namespace RossQC.Regions

/-- Ross, *Quality Control under Markovian Deterioration*, Management Science 17(9):587–596 (1971),
DOI 10.1287/mnsc.17.9.587, §3, p. 590: the two-state production process as an instance of the
general model of §2. State `0` is good, state `1` is bad; revising leads to state `0`.

* `P₀₀ = 1 − π`, `P₀₁ = π`, `P₁₀ = 0`, `P₁₁ = 1`;
* `C₀ = 0`, `C₁ = C`; `I₀ = I₁ = I`; `R₀ = R₁ = R`;
* the discount factor is `β`.

The paper's standing assumption `C < I < R` (and `0 < β < 1`, `0 ≤ π ≤ 1`, `0 < C`) are hypotheses
of the theorems, not part of this data. -/
def twoState (β π C I R : ℝ) : Model (Fin 2) where
  i₀ := 0
  Pm := ![![1 - π, π], ![0, 1]]
  C := ![0, C]
  I := ![I, I]
  R := ![R, R]
  β := β

/-- The belief `(1 − P, P)` that puts probability `P` on the bad state; §3 identifies it with the
number `P ∈ [0, 1]` ("we say that `X_t = P` if `P` is the probability that at the beginning of
period `t` the underlying process is in the bad state", p. 590). -/
def belief (P : ℝ) : Fin 2 → ℝ := ![1 - P, P]

/-- The two-state optimal cost `V_β(P)` of §3: the general `V_β` of the two-state instance,
evaluated at the belief `(1 − P, P)`. -/
noncomputable def V2 (β π C I R : ℝ) (P : ℝ) : ℝ :=
  (twoState β π C I R).Vβ (belief P)

/-- The scalar belief update `TP = P + π − πP` of §3, p. 590. -/
def T2 (π P : ℝ) : ℝ := P + π - π * P

/-- The right side of (3), p. 590, for a function `V` on `[0, 1]`, at the belief `P` and the action
`a`:

* produce: `CP + βV(TP)`;
* inspect: `I + βPV(1) + β(1 − P)V(π)`;
* revise: `R + βV(π)`. -/
def rhs3 (β π C I R : ℝ) (V : ℝ → ℝ) (P : ℝ) : Action → ℝ
  | .produce => C * P + β * V (T2 π P)
  | .inspect => I + β * P * V 1 + β * (1 - P) * V π
  | .revise => R + β * V π

/-- The β-optimal region of the action `a` in the two-state model: the `P ∈ [0, 1]` at which `a`
attains the minimum in (3), i.e. `V_β(P)` equals the right side of (3) for `a`. -/
noncomputable def region2 (β π C I R : ℝ) (a : Action) : Set ℝ :=
  {P | P ∈ Set.Icc (0 : ℝ) 1 ∧ V2 β π C I R P = rhs3 β π C I R (V2 β π C I R) P a}

/-- A stationary rule `δ : [0, 1] → {produce, inspect, revise}` is β-optimal if at every belief
`P ∈ [0, 1]` it selects an action minimizing the right side of (3) (the paper's criterion on p. 588,
quoted from Blackwell [1]: "any rule `R_β` which when in state `P` selects an action which minimizes
the right side of (1) is β-optimal"). -/
noncomputable def IsOptimalRule (β π C I R : ℝ) (δ : ℝ → Action) : Prop :=
  ∀ P ∈ Set.Icc (0 : ℝ) 1, rhs3 β π C I R (V2 β π C I R) P (δ P) = V2 β π C I R P

/-- The four-region rule of Theorem 3.3, p. 590: produce for `P < P₁`, inspect for `P₁ ≤ P < P₂`,
produce for `P₂ ≤ P < P₃`, revise for `P ≥ P₃`. -/
noncomputable def fourRegion (P₁ P₂ P₃ : ℝ) (P : ℝ) : Action :=
  if P < P₁ then .produce
  else if P < P₂ then .inspect
  else if P < P₃ then .produce
  else .revise

end RossQC.Regions
