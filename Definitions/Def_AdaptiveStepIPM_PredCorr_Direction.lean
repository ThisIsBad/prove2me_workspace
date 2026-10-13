import Mathlib
import Definitions.Def_AdaptiveStepIPM_PredCorr_Neighborhoods

open Matrix

namespace AdaptiveStepIPM.PredCorr

/-- System (2): a primal-dual search direction, including its dual multiplier. -/
def SearchDirection {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (x s : Fin n → ℝ) (γ : ℝ)
    (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ) : Prop :=
  (∀ j, s j * dx j + x j * ds j = γ * mu x s - x j * s j) ∧
  A *ᵥ dx = 0 ∧ Aᵀ *ᵥ dy + ds = 0

/-- The primal component of the step (3). -/
def stepX {n : ℕ} (x dx : Fin n → ℝ) (θ : ℝ) : Fin n → ℝ :=
  fun j => x j + θ * dx j

/-- The slack component of the step (3). -/
def stepS {n : ℕ} (s ds : Fin n → ℝ) (θ : ℝ) : Fin n → ℝ :=
  fun j => s j + θ * ds j

/-- The scaled primal direction p in (6). -/
noncomputable def scaledP {n : ℕ} (x s dx : Fin n → ℝ) : Fin n → ℝ :=
  fun j => Real.sqrt (s j / x j) * dx j

/-- The scaled slack direction q in (6). -/
noncomputable def scaledQ {n : ℕ} (x s ds : Fin n → ℝ) : Fin n → ℝ :=
  fun j => Real.sqrt (x j / s j) * ds j

/-- The scaled residual r in (6). -/
noncomputable def scaledR {n : ℕ} (x s : Fin n → ℝ) (γ : ℝ) : Fin n → ℝ :=
  fun j => (γ * mu x s - x j * s j) / Real.sqrt (x j * s j)

/-- The vector Pq = Dₓdₛ of (8). -/
noncomputable def Pq {n : ℕ} (x s dx ds : Fin n → ℝ) : Fin n → ℝ :=
  fun j => scaledP x s dx j * scaledQ x s ds j

/-- The repaired lower bound θ₁ of Lemma 4. At Pq = 0, the limit of the
printed expression is 1/2; real division by zero would instead yield zero. -/
noncomputable def theta1 {n : ℕ} (x s dx ds : Fin n → ℝ) : ℝ :=
  if l2Norm (Pq x s dx ds) = 0 then (1 / 2 : ℝ)
  else min (1 / 2 : ℝ) (Real.sqrt (mu x s / (8 * l2Norm (Pq x s dx ds))))

end AdaptiveStepIPM.PredCorr
