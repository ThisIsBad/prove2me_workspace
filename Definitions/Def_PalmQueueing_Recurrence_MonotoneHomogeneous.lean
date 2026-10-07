import Mathlib

/-!
# Monotone, homogeneous and non-expansive maps (§§2.11.1-2.11.2, pp.154-158)

The four properties a deterministic map `φ : ℝ^K → ℝ^K` may have, exactly as p.154 lists them, and
the stochastic recurrence built from a family of such maps.
-/

namespace PalmQueueing.Recurrence

open MeasureTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `1`, the vector of `ℝ^K` with all its coordinates equal to `1` (p.154). -/
def onesVec (K : ℕ) : Fin K → ℝ := fun _ => 1

/-- `φ` is **homogeneous** (p.154): for all `x ∈ ℝ^K` and `a ∈ ℝ`, `φ(x + a1) = a1 + φ(x)`. -/
def IsHomogeneousMap {K : ℕ} (phi : (Fin K → ℝ) → Fin K → ℝ) : Prop :=
  ∀ (x : Fin K → ℝ) (a : ℝ), phi (x + a • onesVec K) = a • onesVec K + phi x

/-- `φ` is **sub-homogeneous** (p.154): for all `x ∈ ℝ^K` and `a ∈ ℝ₊`,
`φ(x + a1) ≤ a1 + φ(x)`. -/
def IsSubHomogeneousMap {K : ℕ} (phi : (Fin K → ℝ) → Fin K → ℝ) : Prop :=
  ∀ (x : Fin K → ℝ) (a : ℝ), 0 ≤ a → phi (x + a • onesVec K) ≤ a • onesVec K + phi x

/-- `φ` is **monotone** (p.154): `x ≤ y` implies `φ(x) ≤ φ(y)` coordinatewise. -/
def IsMonotoneMap {K : ℕ} (phi : (Fin K → ℝ) → Fin K → ℝ) : Prop :=
  ∀ x y : Fin K → ℝ, x ≤ y → phi x ≤ phi y

/-- `φ` is **non-expansive with respect to the sup-norm** (p.154):
`∀ x, y ∈ ℝ^K, ‖φ(x) − φ(y)‖_∞ ≤ ‖x − y‖_∞`. -/
def IsNonExpansiveMap {K : ℕ} (phi : (Fin K → ℝ) → Fin K → ℝ) : Prop :=
  ∀ x y : Fin K → ℝ, ‖phi x - phi y‖ ≤ ‖x - y‖

/-- The stochastic recurrence of §2.11.2 (p.158) with state space `ℝ^K`:
`X^{[Y]}_{n+1} = h(X^{[Y]}_n, ξ_n)`, with `X^{[Y]}_0 = Y` and `{ξ_n}` compatible with the shift.
It is **monotone and homogeneous** when for all `ξ` the map `X ↦ h(X, ξ)` is. -/
def IsMHRecurrence {K : ℕ} {F : Type*} (h : (Fin K → ℝ) → F → Fin K → ℝ) : Prop :=
  ∀ z : F, IsMonotoneMap (fun X => h X z) ∧ IsHomogeneousMap (fun X => h X z)

/-- `X^{[Y]}_n`, the recurrence run from the initial condition `Y` (p.158). -/
noncomputable def mhIterate {K : ℕ} {F : Type*} (h : (Fin K → ℝ) → F → Fin K → ℝ)
    (xi : ℕ → Ω → F) (Y : Ω → Fin K → ℝ) : ℕ → Ω → Fin K → ℝ
  | 0 => Y
  | (n + 1) => fun ω => h (mhIterate h xi Y n ω) (xi n ω)

end PalmQueueing.Recurrence
