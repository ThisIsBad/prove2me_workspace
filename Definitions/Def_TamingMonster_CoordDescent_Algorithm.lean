import Mathlib
import Definitions.Def_TamingMonster_CoordDescent_Setting

namespace TamingMonster.CoordDescent

variable {X : Type*} {K t : ℕ}

/-- Step 3 of Algorithm 2 (p. 6): `V_π(Q) = Ê_{x∼H_t}[1 / Q^μ(π(x) | x)]`. -/
noncomputable def Vfun (Pi : Finset (X → Fin K)) (H : History X K t) (μ : ℝ) (Q : Pi → ℝ)
    (π : Pi) : ℝ :=
  empExp H (fun x => 1 / smoothedProj Pi μ Q x ((π : X → Fin K) x))

/-- Step 3 of Algorithm 2: `S_π(Q) = Ê_{x∼H_t}[1 / (Q^μ(π(x) | x))²]`. -/
noncomputable def Sfun (Pi : Finset (X → Fin K)) (H : History X K t) (μ : ℝ) (Q : Pi → ℝ)
    (π : Pi) : ℝ :=
  empExp H (fun x => 1 / (smoothedProj Pi μ Q x ((π : X → Fin K) x)) ^ 2)

/-- Step 3 of Algorithm 2: `D_π(Q) = V_π(Q) − (2K + b_π)`. -/
noncomputable def Dfun (Pi : Finset (X → Fin K)) (H : History X K t) (μ : ℝ) (Q : Pi → ℝ)
    (π : Pi) : ℝ :=
  Vfun Pi H μ Q π - (2 * (K : ℝ) + bCoef Pi H μ (π : X → Fin K))

/-- The quantity `∑_π Q(π)(2K + b_π)` tested in Step 4 of Algorithm 2. -/
noncomputable def weightedMass (Pi : Finset (X → Fin K)) (H : History X K t) (μ : ℝ)
    (Q : Pi → ℝ) : ℝ :=
  ∑ π, Q π * (2 * (K : ℝ) + bCoef Pi H μ (π : X → Fin K))

/-- Eq. (4): `c = 2K / ∑_π Q(π)(2K + b_π)`. -/
noncomputable def scaleFactor (Pi : Finset (X → Fin K)) (H : History X K t) (μ : ℝ)
    (Q : Pi → ℝ) : ℝ :=
  2 * (K : ℝ) / weightedMass Pi H μ Q

/-- Steps 4–6 of Algorithm 2: if `∑_π Q(π)(2K + b_π) > 2K`, replace `Q` by `cQ` with `c` as in
Eq. (4); otherwise leave `Q` unchanged. -/
noncomputable def rescale (Pi : Finset (X → Fin K)) (H : History X K t) (μ : ℝ)
    (Q : Pi → ℝ) : Pi → ℝ :=
  if 2 * (K : ℝ) < weightedMass Pi H μ Q then
    fun π => scaleFactor Pi H μ Q * Q π
  else Q

/-- Step 8 of Algorithm 2: `α_π(Q) = (V_π(Q) + D_π(Q)) / (2(1 − Kμ) S_π(Q))`. -/
noncomputable def alphaStep (Pi : Finset (X → Fin K)) (H : History X K t) (μ : ℝ)
    (Q : Pi → ℝ) (π : Pi) : ℝ :=
  (Vfun Pi H μ Q π + Dfun Pi H μ Q π) / (2 * (1 - (K : ℝ) * μ) * Sfun Pi H μ Q π)

open Classical in
/-- Step 8 of Algorithm 2 applied to `Q`: add `α_π(Q)` to `Q(π)` and leave all other weights
unchanged. -/
noncomputable def addAlpha (Pi : Finset (X → Fin K)) (H : History X K t) (μ : ℝ)
    (Q : Pi → ℝ) (π : Pi) : Pi → ℝ :=
  Function.update Q π (Q π + alphaStep Pi H μ Q π)

/-- One pass through the loop of Algorithm 2 that ends in Step 8 with policy `π`: rescale `Q`
(Steps 4–6), then add `α_π` to the coordinate `π` of the rescaled weights (Step 8). -/
noncomputable def cdStep (Pi : Finset (X → Fin K)) (H : History X K t) (μ : ℝ)
    (Q : Pi → ℝ) (π : Pi) : Pi → ℝ :=
  addAlpha Pi H μ (rescale Pi H μ Q) π

/-- A run of Algorithm 2 with `n` executions of Step 8, started from `Q_init` (Step 1):
`Qs 0 = Q_init`, and for every `k < n` some policy `π` has `D_π(rescale (Qs k)) > 0` (the test of
Step 7 succeeds, with `π` any policy passing it) and `Qs (k+1)` is the result of Step 8 for that
`π`. -/
def IsRun (Pi : Finset (X → Fin K)) (H : History X K t) (μ : ℝ) (Qinit : Pi → ℝ) (n : ℕ)
    (Qs : ℕ → Pi → ℝ) : Prop :=
  Qs 0 = Qinit ∧
  ∀ k < n, ∃ π : Pi, 0 < Dfun Pi H μ (rescale Pi H μ (Qs k)) π ∧
    Qs (k + 1) = cdStep Pi H μ (Qs k) π

/-- The loop, entered with weights `Q`, halts at Step 10: after Steps 4–6 no policy has
`D_π > 0`. Its output is then `rescale Q`. -/
def HaltsAt (Pi : Finset (X → Fin K)) (H : History X K t) (μ : ℝ) (Q : Pi → ℝ) : Prop :=
  ∀ π : Pi, Dfun Pi H μ (rescale Pi H μ Q) π ≤ 0

end TamingMonster.CoordDescent
