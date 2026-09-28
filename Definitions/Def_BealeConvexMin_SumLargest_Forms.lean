import Mathlib
import Definitions.Def_BealeConvexMin_SumLargest_sumLargest

namespace BealeConvexMin.SumLargest

/-- Beale (1955), Theorem 1 (a), p. 179: the data of the setting
`A = A_0 + Σ_l A_l z_l + Σ_{f=1}^{s} φ_f u_f`, `L_0 = c_00 + Σ_l c_0l z_l + Σ_{f=1}^{s} θ_f u_f`.

The variables are `z : Fin r → ℝ` (the paper's `z_l`; the paper leaves the range of `l` open, so
`r` is arbitrary, possibly `0`) and `u : Fin s → ℝ`. The paper's `u_f`, `φ_f`, `θ_f` for
`f = 1, …, s` are Lean's `u f`, `φ f`, `θ f` for `f = 0, …, s-1`. -/
structure Forms (r s : ℕ) where
  /-- the constant term `A_0` of `A` -/
  A0 : ℝ
  /-- the coefficients `A_l` of `z_l` in `A` -/
  A : Fin r → ℝ
  /-- the coefficients `φ_f` of `u_f` in `A` -/
  φ : Fin s → ℝ
  /-- the constant term `c_00` of `L_0` -/
  c00 : ℝ
  /-- the coefficients `c_0l` of `z_l` in `L_0` -/
  c0 : Fin r → ℝ
  /-- the coefficients `θ_f` of `u_f` in `L_0` -/
  θ : Fin s → ℝ

namespace Forms

variable {r s : ℕ} (P : Forms r s)

/-- The linear form `A = A_0 + Σ_l A_l z_l + Σ_{f=1}^{s} φ_f u_f`. -/
def formA (z : Fin r → ℝ) (u : Fin s → ℝ) : ℝ :=
  P.A0 + ∑ l, P.A l * z l + ∑ f, P.φ f * u f

/-- The linear form `L_0 = c_00 + Σ_l c_0l z_l + Σ_{f=1}^{s} θ_f u_f`. -/
def L0 (z : Fin r → ℝ) (u : Fin s → ℝ) : ℝ :=
  P.c00 + ∑ l, P.c0 l * z l + ∑ f, P.θ f * u f

/-- The family `L_0, L_1, …, L_s` with `L_f = L_0 - u_f` for `f = 1, …, s`: index `0` is `L_0`,
and index `f.succ` (for `f : Fin s`, the paper's `f + 1`) is `L_0 - u f`. -/
def L (z : Fin r → ℝ) (u : Fin s → ℝ) : Fin (s + 1) → ℝ :=
  fun i => Fin.cases (motive := fun _ => ℝ) (P.L0 z u) (fun f => P.L0 z u - u f) i

/-- The objective: `C` equals `A` plus the sum of the `τ` largest of `L_0, L_1, …, L_s`. -/
noncomputable def C (τ : ℕ) (z : Fin r → ℝ) (u : Fin s → ℝ) : ℝ :=
  P.formA z u + sumLargest τ (P.L z u)

/-- The conditions (4.5) of Theorem 1 (a), p. 179, where `F` is the set of indices `l` for which
`z_l` is free:
* `A_l + τ c_0l ≥ 0` for all `l`,
* `A_l + τ c_0l = 0` for all `l` such that `z_l` is free,
* `0 ≤ φ_f + τ θ_f ≤ 1` for all `f`,
* `τ - 1 ≤ Σ_{f=1}^{s} (φ_f + τ θ_f) ≤ τ`. -/
def Cond45 (τ : ℕ) (F : Finset (Fin r)) : Prop :=
  (∀ l, 0 ≤ P.A l + (τ : ℝ) * P.c0 l) ∧
  (∀ l ∈ F, P.A l + (τ : ℝ) * P.c0 l = 0) ∧
  (∀ f, 0 ≤ P.φ f + (τ : ℝ) * P.θ f ∧ P.φ f + (τ : ℝ) * P.θ f ≤ 1) ∧
  ((τ : ℝ) - 1 ≤ ∑ f, (P.φ f + (τ : ℝ) * P.θ f) ∧ ∑ f, (P.φ f + (τ : ℝ) * P.θ f) ≤ (τ : ℝ))

/-- "`C` is minimized when all the `z_l` and `u_f` vanish": `C(0, 0) ≤ C(z, u)` for every `z, u`
with `z_l ≥ 0` for every `l ∉ F` (the `z_l` with `l ∈ F` and all the `u_f` are free). This is a
global minimum over the feasible region. -/
def IsMinimizedAtZero (τ : ℕ) (F : Finset (Fin r)) : Prop :=
  ∀ (z : Fin r → ℝ) (u : Fin s → ℝ), (∀ l, l ∉ F → 0 ≤ z l) → P.C τ 0 0 ≤ P.C τ z u

end Forms

end BealeConvexMin.SumLargest
