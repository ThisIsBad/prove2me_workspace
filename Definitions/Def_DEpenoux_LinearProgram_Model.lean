import Mathlib
import Definitions.Def_BertsekasSSPModel

namespace DEpenoux.LinearProgram

open Finset

/-- d'Epenoux 1963, §1, pp. 98–99: the admissible potentials at initial stock `i`, namely the
potentials `j` with `i ≤ j ≤ σ` (stock levels and potentials are `0, 1, …, σ`). -/
def admissible (σ : ℕ) (i : Fin (σ + 1)) : Finset (Fin (σ + 1)) :=
  univ.filter (fun j => i ≤ j)

/-- d'Epenoux 1963, §1, p. 99: the production–inventory model as a finite discounted decision
model, an instance of the published `BertsekasSSPModel`. States are the stock levels
`i = 0, …, σ`, controls are the potentials `j`, admissible when `i ≤ j`; the transition
probability from stock `i` under potential `j` to end stock `s` is `p j s` (it depends on the
potential only); the one-period expected cost is `d i j`. The hypotheses say that every row
`p j ·` is a probability vector. -/
def model (σ : ℕ) (p d : Fin (σ + 1) → Fin (σ + 1) → ℝ)
    (hp0 : ∀ j s, 0 ≤ p j s) (hp1 : ∀ j, ∑ s, p j s = 1) :
    BertsekasSSPModel (σ + 1) (Fin (σ + 1)) where
  U i := admissible σ i
  hU i := ⟨i, by simp [admissible]⟩
  p _ j s := p j s
  g i j := d i j
  hp_nonneg _ j s := hp0 j s
  hp_sum _ j _ := le_of_eq (hp1 j)

/-- d'Epenoux 1963, §1, p. 99: a strategy `J` fixes the potential `J i` from the initial stock
`i` only, and must be admissible: `i ≤ J i`. -/
def IsStrategy {σ : ℕ} (J : Fin (σ + 1) → Fin (σ + 1)) : Prop :=
  ∀ i, i ≤ J i

/-- d'Epenoux 1963, §2, pp. 100–101: the transition matrix `P_J` of a strategy `J`,
`(P_J)_{is} = p_{J(i) s}`. -/
def stratMatrix {σ : ℕ} (p : Fin (σ + 1) → Fin (σ + 1) → ℝ) (J : Fin (σ + 1) → Fin (σ + 1)) :
    Matrix (Fin (σ + 1)) (Fin (σ + 1)) ℝ :=
  fun i s => p (J i) s

/-- d'Epenoux 1963, §5, p. 104, and (9), p. 105:
`U_ij = u_i − λ ∑_s p_js u_s − d_ij`. -/
def Uij {σ : ℕ} (p d : Fin (σ + 1) → Fin (σ + 1) → ℝ) (lam : ℝ) (u : Fin (σ + 1) → ℝ)
    (i j : Fin (σ + 1)) : ℝ :=
  u i - lam * ∑ s, p j s * u s - d i j

/-- d'Epenoux 1963, §5, p. 104, condition (A), i.e. the constraints (9) of p. 105:
`U_ij ≤ 0` for every stock level `i` and every admissible potential `j ≥ i`. -/
def setA {σ : ℕ} (p d : Fin (σ + 1) → Fin (σ + 1) → ℝ) (lam : ℝ) : Set (Fin (σ + 1) → ℝ) :=
  {u | ∀ i j, i ≤ j → Uij p d lam u i j ≤ 0}

/-- d'Epenoux 1963, §5, p. 104, condition (B): `∏_j U_ij = 0` for every `i`, the product over
the admissible potentials `j ≥ i`. -/
def setB {σ : ℕ} (p d : Fin (σ + 1) → Fin (σ + 1) → ℝ) (lam : ℝ) : Set (Fin (σ + 1) → ℝ) :=
  {u | ∀ i, ∏ j ∈ admissible σ i, Uij p d lam u i j = 0}

/-- d'Epenoux 1963, §5, p. 105, program (P₂): `u` is an optimal solution of
"maximize `(1 − λ) ∑_i c_i u_i` under the constraints (9)". -/
def IsP2Optimal {σ : ℕ} (p d : Fin (σ + 1) → Fin (σ + 1) → ℝ) (lam : ℝ)
    (c : Fin (σ + 1) → ℝ) (u : Fin (σ + 1) → ℝ) : Prop :=
  u ∈ setA p d lam ∧
    ∀ v ∈ setA p d lam, (1 - lam) * ∑ i, c i * v i ≤ (1 - lam) * ∑ i, c i * u i

end DEpenoux.LinearProgram
