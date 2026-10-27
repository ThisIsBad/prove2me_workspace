import Mathlib

noncomputable section

namespace WHAdditivity.Renyi

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable

/-- Joint basis labels of ⊗_j ℂ^{d_j}; site j of the paper is `j : Fin N` (counted from 0). -/
abbrev Config {N : ℕ} (d : Fin N → ℕ) : Type := (j : Fin N) → Fin (d j)

/-- Basis labels of the sites in Λ ⊂ {1, …, N}. -/
abbrev SubConfig {N : ℕ} (d : Fin N → ℕ) (Λ : Finset (Fin N)) : Type := (j : Λ) → Fin (d j)

/-- (6), p. 2, extended linearly: Γ_d(X) = (Tr X · 𝟙 − Xᵀ)/(d − 1); on a trace-one ρ this is
(𝟙 − ρᵀ)/(d − 1). -/
def wernerHolevo (d : ℕ) (X : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  ((d : ℂ) - 1)⁻¹ • (X.trace • (1 : Matrix (Fin d) (Fin d) ℂ) - Xᵀ)

/-- ⊗_j Φ_j on ⊗_j ℂ^{d_j}, through matrix units:
⟨y|(⊗_j Φ_j)(X)|y′⟩ = Σ_{x,x′} X_{x x′} Π_j ⟨y_j|Φ_j(|x_j⟩⟨x′_j|)|y′_j⟩, for any family Φ. -/
def tensorChannel {N : ℕ} (d : Fin N → ℕ)
    (Φ : (j : Fin N) → Matrix (Fin (d j)) (Fin (d j)) ℂ → Matrix (Fin (d j)) (Fin (d j)) ℂ)
    (X : Matrix (Config d) (Config d) ℂ) : Matrix (Config d) (Config d) ℂ :=
  Matrix.of fun y y' => ∑ x : Config d, ∑ x' : Config d,
    X x x' * ∏ j, Φ j (Matrix.single (x j) (x' j) 1) (y j) (y' j)

/-- ‖v‖ = 1. -/
def IsUnitVector {ι : Type*} [Fintype ι] (v : ι → ℂ) : Prop := ∑ i, Complex.normSq (v i) = 1

/-- |v⟩⟨v|, with entries v_i · conj v_k. -/
def pureState {ι : Type*} (v : ι → ℂ) : Matrix ι ι ℂ := Matrix.vecMulVec v (star v)

/-- ρ is a density matrix: positive semidefinite with trace one. -/
def IsDensity {ι : Type*} [Fintype ι] (ρ : Matrix ι ι ℂ) : Prop := ρ.PosSemidef ∧ ρ.trace = 1

/-- S(ρ) = −Tr ρ log ρ (natural log, 0 log 0 = 0), by the continuous functional calculus. -/
def vonNeumannEntropy {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : Matrix ι ι ℂ) : ℝ :=
  (cfc Real.negMulLog ρ).trace.re

/-- Tr ρᵖ, by the continuous functional calculus. -/
def traceRpow {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℝ) (ρ : Matrix ι ι ℂ) : ℝ :=
  (cfc (fun x : ℝ => x ^ p) ρ).trace.re

/-- S_p(ρ) = −(1/(p − 1)) log Tr ρᵖ for p ≠ 1, and S_1 = S (the paper's extension to p = 1). -/
def renyiEntropy {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℝ) (ρ : Matrix ι ι ℂ) : ℝ :=
  if p = 1 then vonNeumannEntropy ρ else (1 - p)⁻¹ * Real.log (traceRpow p ρ)

/-- The values S_p(Φ(|φ⟩⟨φ|)) over all unit vectors φ (entangled ones included when ι is a
product of sites). -/
def outputEntropies {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] (p : ℝ)
    (Φ : Matrix ι ι ℂ → Matrix κ κ ℂ) : Set ℝ :=
  {s | ∃ φ : ι → ℂ, IsUnitVector φ ∧ s = renyiEntropy p (Φ (pureState φ))}

/-- (1), p. 1: MEO_p(Φ) = inf_{‖φ‖=1} S_p(Φ(|φ⟩⟨φ|)). Theorems using it conclude `BddBelow`
of `outputEntropies p Φ`. -/
def minOutputEntropy {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] (p : ℝ)
    (Φ : Matrix ι ι ℂ → Matrix κ κ ℂ) : ℝ :=
  sInf (outputEntropies p Φ)

/-- The labels of y on the sites in Λ. -/
def restrict {N : ℕ} (d : Fin N → ℕ) (Λ : Finset (Fin N)) (y : Config d) : SubConfig d Λ :=
  fun j => y j

/-- ρ_Λ = Tr_{Λᶜ} ρ, the reduced matrix of ρ on the sites in Λ. -/
def reducedMatrix {N : ℕ} (d : Fin N → ℕ) (Λ : Finset (Fin N))
    (ρ : Matrix (Config d) (Config d) ℂ) : Matrix (SubConfig d Λ) (SubConfig d Λ) ℂ :=
  Matrix.of fun a b => ∑ z : Config d, ∑ z' : Config d,
    if restrict d Λ z = a ∧ restrict d Λ z' = b ∧ (∀ j, j ∉ Λ → z j = z' j) then ρ z z' else 0

/-- σ ⊗ 𝟙_{Λᶜ}, in the natural site order. -/
def tensorIdentity {N : ℕ} (d : Fin N → ℕ) (Λ : Finset (Fin N))
    (σ : Matrix (SubConfig d Λ) (SubConfig d Λ) ℂ) : Matrix (Config d) (Config d) ℂ :=
  Matrix.of fun y y' =>
    if ∀ j, j ∉ Λ → y j = y' j then σ (restrict d Λ y) (restrict d Λ y') else 0

/-- ⊗_j ρ_j. -/
def tensorMatrix {N : ℕ} (d : Fin N → ℕ) (ρ : (j : Fin N) → Matrix (Fin (d j)) (Fin (d j)) ℂ) :
    Matrix (Config d) (Config d) ℂ :=
  Matrix.of fun y y' => ∏ j, ρ j (y j) (y' j)

end WHAdditivity.Renyi
