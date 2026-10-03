import Mathlib

namespace Disjunctive.RayCGLP

/-- `Â`, the `n×n` submatrix of `Ã` whose rows are `ι 0, …, ι (n-1)` (restated locally from
`08-cut-correspondence`/`09-simplex-tableau`). -/
def Ahat {n : ℕ} {M : Type*} (Atil : Matrix M (Fin n) ℝ) (ι : Fin n → M) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => Atil (ι i) j

/-- `b̂`, the subvector of `b̃` corresponding to `Â` (restated locally). -/
def Bhat {n : ℕ} {M : Type*} (btil : M → ℝ) (ι : Fin n → M) : Fin n → ℝ :=
  fun i => btil (ι i)

/-- `ā_k0 := e_k Â⁻¹ b̂` (restated locally). -/
noncomputable def Abar0 {n : ℕ} {M : Type*} [DecidableEq (Fin n)] (Atil : Matrix M (Fin n) ℝ)
    (btil : M → ℝ) (ι : Fin n → M) (k : Fin n) : ℝ :=
  (Ahat Atil ι)⁻¹.mulVec (Bhat btil ι) k

/-- `ā_kj := -(Â⁻¹)_{kj}` (restated locally). -/
noncomputable def Abar {n : ℕ} {M : Type*} [DecidableEq (Fin n)] (Atil : Matrix M (Fin n) ℝ)
    (ι : Fin n → M) (k j : Fin n) : ℝ :=
  -((Ahat Atil ι)⁻¹) k j

/-- The surplus (slack) value at an arbitrary row `i : M` (restated locally from
`09-simplex-tableau`'s `SurplusM`). -/
def SurplusM {n : ℕ} {M : Type*} (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (i : M)
    (x : Fin n → ℝ) : ℝ :=
  dotProduct (Atil i) x - btil i

/-- `γ_l := -ā_kl/ā_il` (restated locally from `09-simplex-tableau`'s `GammaOf`). -/
noncomputable def GammaOf {n : ℕ} {M : Type*} [DecidableEq (Fin n)] (Atil : Matrix M (Fin n) ℝ)
    (ι : Fin n → M) (k i l : Fin n) : ℝ :=
  -(Abar Atil ι k l) / Abar Atil ι i l

/-- One step of rule (b) of Theorem 10.1: the sign of `ā_{k,·}` flips between two consecutive
indices of the exchange chain, matching (b1) (positive to negative) or (b2) (negative to
positive) combined via the flip itself (Balas §10.1, p. 122). -/
def IsSignFlipStep {n : ℕ} {M : Type*} [DecidableEq (Fin n)] (Atil : Matrix M (Fin n) ℝ)
    (ι : Fin n → M) (k jh jh' : Fin n) : Prop :=
  (0 < Abar Atil ι k jh ∧ Abar Atil ι k jh' < 0) ∨ (Abar Atil ι k jh < 0 ∧ 0 < Abar Atil ι k jh')

/-- The simple disjunctive cut from the disjunction `z ≤ 0 ∨ z ≥ 1` applied to the *combined*
source row `(10.1)_γ` (Balas §10.1, p. 122, eq. (10.1)): `z := x_k + γx_i`, row coefficients
`ā_{kj}+γā_{ij}`, right-hand side `ā_{k0}+γā_{i0}`. -/
def CombinedCutSet {n : ℕ} {M : Type*} [Fintype M] [DecidableEq (Fin n)]
    (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (ι : Fin n → M) (k i : Fin n)
    (J : Finset (Fin n)) (γ : ℝ) : Set (Fin n → ℝ) :=
  {x | (Abar0 Atil btil ι k + γ * Abar0 Atil btil ι i) *
        (1 - (Abar0 Atil btil ι k + γ * Abar0 Atil btil ι i)) ≤
      ∑ j ∈ J, max ((1 - (Abar0 Atil btil ι k + γ * Abar0 Atil btil ι i)) *
            (Abar Atil ι k j + γ * Abar Atil ι i j))
          (-(Abar0 Atil btil ι k + γ * Abar0 Atil btil ι i) *
            (Abar Atil ι k j + γ * Abar Atil ι i j)) *
        SurplusM Atil btil (ι j) x}

end Disjunctive.RayCGLP
