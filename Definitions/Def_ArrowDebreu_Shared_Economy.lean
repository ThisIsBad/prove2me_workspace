import Mathlib

namespace ArrowDebreu.Shared

/-- **The data of a competitive economy** (Arrow & Debreu, *Existence of an Equilibrium for a
Competitive Economy*, Econometrica 22 (1954), §1.2.2, §1.3.0, §1.3.1, §1.3.2, pp. 267–270,
PDF pp. 4–7).

There are `l` commodities, `n` production units and `m` consumption units. Commodity vectors are
elements of `R^l = Fin l → ℝ`.

* `Y j` is the set of possible production plans of producer `j` (§1.2.2; inputs are negative
  components);
* `X i` is the set of consumption vectors available to consumer `i` (§1.3.0);
* `u i` is the utility indicator of consumer `i` (§1.3.1);
* `ζ i` is the vector of initial holdings of consumer `i` (§1.3.2);
* `α i j` is the share of consumer `i` in the profit of producer `j` (§1.3.2).

**Formalization Note.** The utility `u i` is a total function on `R^l`; only its values on `X i`
matter, and every assumption on it (Assumption III) quantifies over `X i` only. -/
structure Economy (l m n : ℕ) where
  /-- Production sets `Y_j ⊆ R^l`. -/
  Y : Fin n → Set (Fin l → ℝ)
  /-- Consumption sets `X_i ⊆ R^l`. -/
  X : Fin m → Set (Fin l → ℝ)
  /-- Utility indicators `u_i`. -/
  u : Fin m → (Fin l → ℝ) → ℝ
  /-- Initial holdings `ζ_i ∈ R^l`. -/
  ζ : Fin m → Fin l → ℝ
  /-- Profit shares `α_{ij}`. -/
  α : Fin m → Fin n → ℝ

/-- The nonnegative orthant `Ω = {x | x ∈ R^l, x ≧ 0}` (§1.2.1, p. 267, PDF p. 4). The order on
`Fin l → ℝ` is componentwise, so `0 ≤ x` is the paper's `x ≧ 0`. -/
def Ω (l : ℕ) : Set (Fin l → ℝ) := {x | 0 ≤ x}

/-- `−A = {x | −x ∈ A}` (§1.2.1, p. 267, PDF p. 4). -/
def negSet {l : ℕ} (A : Set (Fin l → ℝ)) : Set (Fin l → ℝ) := {x | -x ∈ A}

/-- The aggregate production set `Y = Σ_{j=1}^n Y_j` (§1.2.2, p. 267, PDF p. 4), the set sum of
§1.2.1: the vectors `Σ_j y_j` with `y_j ∈ Y_j` for every `j`. With `n = 0` it is `{0}`. -/
def aggProd {l m n : ℕ} (E : Economy l m n) : Set (Fin l → ℝ) :=
  {v | ∃ y : Fin n → Fin l → ℝ, (∀ j, y j ∈ E.Y j) ∧ v = ∑ j, y j}

/-- The price simplex `P = {p | p ∈ R^l, p ≧ 0, Σ_{h=1}^l p_h = 1}` (Condition 3, §1.4.0, p. 271,
PDF p. 8). It is empty when `l = 0`. -/
def priceSimplex (l : ℕ) : Set (Fin l → ℝ) := {p | 0 ≤ p ∧ ∑ h, p h = 1}

/-- The income of consumer `i` at prices `p` when producer `j` operates `y j`:
`p·ζ_i + Σ_{j=1}^n α_{ij} p·y_j` (Condition 2, §1.3.3, p. 271, PDF p. 8). Here `u·v` is the inner
product `Σ_h u_h v_h` (footnote 4, p. 268), written `⬝ᵥ` (`dotProduct`). -/
def income {l m n : ℕ} (E : Economy l m n) (p : Fin l → ℝ) (y : Fin n → Fin l → ℝ) (i : Fin m) : ℝ :=
  p ⬝ᵥ E.ζ i + ∑ j, E.α i j * (p ⬝ᵥ y j)

/-- The excess demand `z = x − y − ζ` with `x = Σ_i x_i`, `y = Σ_j y_j`, `ζ = Σ_i ζ_i` (§1.4.1,
p. 271, PDF p. 8). -/
def excessDemand {l m n : ℕ} (E : Economy l m n) (x : Fin m → Fin l → ℝ)
    (y : Fin n → Fin l → ℝ) : Fin l → ℝ :=
  ∑ i, x i - ∑ j, y j - ∑ i, E.ζ i

end ArrowDebreu.Shared
