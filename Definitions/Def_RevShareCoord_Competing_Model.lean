import Mathlib
import Definitions.Def_RevShareCoord_Competing_Game

/-!
# The competing-retailers model of Sec. 3.2 and its coordinating wholesale prices

Cachon–Lariviere, *Supply Chain Coordination with Revenue-Sharing Contracts: Strengths and
Limitations*, working paper (June 2000), Sec. 3.2, pp. 12–13.

**Index convention.** `dR i j q` is the partial derivative `∂R_j/∂q_i` at `q`, which the paper
writes `R_j^i(q̄)`: the first index (the paper's superscript) is the variable differentiated,
the second (the paper's subscript) the revenue function.
-/

namespace RevShareCoord.Competing

open Finset

/-- The standing assumptions of Sec. 3.2 (pp. 12–13) on the revenue functions `Rᵢ` of the `n`
locations and the unit cost `c`.

* `R i q` is the revenue `Rᵢ(q̄)` at location `i`; `dR i j q` is `R_j^i(q̄) = ∂R_j/∂q_i`, given at
  every profile with all quantities positive.
* `Rᵢ` is continuous (on profiles with nonnegative entries).
* `∂²Rᵢ/∂qᵢ∂qⱼ ≤ 0` for `j ≠ i`, encoded as: the marginal revenue `R_i^i` at `i` does not increase
  when the quantity at another location `j` increases (the paper's own reading: "increasing the
  quantity at location j reduces the marginal revenue … at i").
* "`Rᵢ(q̄)` is unimodal in `qᵢ`" is read as: for every profile of nonnegative quantities, `Rᵢ` is
  concave in its own quantity `qᵢ ∈ [0, ∞)`.
* `c > 0`.

The assumption on `q_i^δ` (marginal revenue eventually below any `δ > 0`) is used by the paper
only for the existence of an equilibrium and is not part of this structure. -/
structure Model (n : ℕ) where
  /-- Revenue `Rᵢ(q̄)` at location `i`. -/
  R : Fin n → (Fin n → ℝ) → ℝ
  /-- `dR i j q = R_j^i(q̄) = ∂R_j/∂q_i (q̄)`. -/
  dR : Fin n → Fin n → (Fin n → ℝ) → ℝ
  /-- Unit cost `c` of a unit, at any location. -/
  c : ℝ
  /-- `c > 0`. -/
  c_pos : 0 < c
  /-- `Rᵢ` is continuous on the nonnegative orthant. -/
  cont : ∀ i, ContinuousOn (R i) {q | ∀ k, 0 ≤ q k}
  /-- At every profile with all quantities positive, `dR i j q` is the partial derivative of
  `R_j` with respect to `q_i`. -/
  hasPartial : ∀ q : Fin n → ℝ, (∀ k, 0 < q k) → ∀ i j,
    HasDerivAt (fun t => R j (Function.update q i t)) (dR i j q) (q i)
  /-- `∂²Rᵢ/∂qᵢ∂qⱼ ≤ 0` for `j ≠ i`: raising `q_j` does not raise `R_i^i`. -/
  cross : ∀ q : Fin n → ℝ, (∀ k, 0 < q k) → ∀ i j, j ≠ i → ∀ t, q j ≤ t →
    dR i i (Function.update q j t) ≤ dR i i q
  /-- `Rᵢ` is concave in its own quantity `qᵢ ≥ 0` (reading of "unimodal in `qᵢ`"). -/
  concave_own : ∀ (i : Fin n) (q : Fin n → ℝ), (∀ k, 0 ≤ q k) →
    ConcaveOn ℝ (Set.Ici 0) (fun t => R i (Function.update q i t))

namespace Model

variable {n : ℕ} (M : Model n)

/-- The first-order system (6) of the integrated channel (Sec. 3.2, p. 12):
`R_i^i(q̄) + Σ_{j≠i} R_j^i(q̄) = c` for `i = 1, …, n`. -/
def FOC (q : Fin n → ℝ) : Prop :=
  ∀ i, M.dR i i q + ∑ j ∈ univ.erase i, M.dR i j q = M.c

/-- The coordinating wholesale prices `w_i^I = c − Σ_{j≠i} R_j^i(q̄^I)` (Sec. 3.2, p. 13),
computed at the profile `qI`. -/
def wI (qI : Fin n → ℝ) (i : Fin n) : ℝ :=
  M.c - ∑ j ∈ univ.erase i, M.dR i j qI

end Model

end RevShareCoord.Competing
