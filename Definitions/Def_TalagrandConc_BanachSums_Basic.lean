import Mathlib
import Definitions.Def_Komlos_RandomSignModel

namespace TalagrandConc.BanachSums

open MeasureTheory
open scoped ENNReal Classical

/-- The Rademacher sign attached to a fair coin: `ε = 1` for `true`, `ε = -1` for `false`.
Under `Komlos.spMeasure N` the signs `sgn (ε i)` are independent with
`P(ε_i = 1) = P(ε_i = -1) = 1/2` (Talagrand 1995, p. 196). -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- The Rademacher sum `Σ_{i ≤ N} ε_i x_i` of vectors `x = (x_i)_{i ≤ N}` in `W`
for a sign pattern `ε ∈ {true, false}^N` (Talagrand 1995, Eq. (13.3), p. 196). -/
def signedSum {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {N : ℕ}
    (ε : Fin N → Bool) (x : Fin N → W) : W :=
  ∑ i, sgn (ε i) • x i

/-- `Z(x) = E_ε ‖Σ_{i ≤ N} ε_i x_i‖` (Talagrand 1995, Eq. (13.4), p. 196, and the function `Z`
on `Ω^N`, `Ω = W`, in the proof of Proposition 13.1, p. 197): the average of
`‖Σ ε_i x_i‖` over the `2^N` sign patterns, i.e. the expectation under the uniform measure
`Komlos.spMeasure N`. A finite average, so always a finite real number. -/
noncomputable def Eeps {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {N : ℕ}
    (x : Fin N → W) : ℝ :=
  ∑ ε : Fin N → Bool, ((2 : ℝ) ^ N)⁻¹ * ‖signedSum ε x‖

/-- `σ²(x) = sup { Σ_{i ≤ N} w*(x_i)² ; w* ∈ W*, ‖w*‖ ≤ 1 }` (Talagrand 1995, p. 199; also
Eq. (13.10), p. 198). The supremum is over the closed unit ball of the dual `W →L[ℝ] ℝ`
(operator norm); the family is nonempty (`w* = 0`) and bounded above by `Σ ‖x_i‖²`, so the
real `⨆` is the true supremum. -/
noncomputable def sigmaSq {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {N : ℕ}
    (x : Fin N → W) : ℝ :=
  ⨆ w : {w : W →L[ℝ] ℝ // ‖w‖ ≤ 1}, ∑ i, (w.1 (x i)) ^ 2

/-- `‖x_i‖* = sup { t ; card { j ≤ N ; ‖x_j‖ ≥ t } ≥ i }` (Talagrand 1995, p. 196), indexed
`1 ≤ i ≤ N` as in the paper; it is the `i`-th largest of `‖x_1‖, …, ‖x_N‖`. For
`1 ≤ i ≤ N` the set is nonempty and bounded above, so `sSup` is the true supremum. Outside
`1 ≤ i ≤ N` the value is set to `0` (the sequence is padded with zeros), so that
`Σ_{i ≤ k} ‖x_i‖*` for `k ≥ N` is the sum of all `‖x_i‖`. -/
noncomputable def normRearr {W : Type*} [NormedAddCommGroup W] {N : ℕ}
    (x : Fin N → W) (i : ℕ) : ℝ :=
  if 1 ≤ i ∧ i ≤ N then
    sSup {t : ℝ | i ≤ (Finset.univ.filter (fun j => t ≤ ‖x j‖)).card}
  else 0

/-- `Σ_{i ≤ k} ‖x_i‖*`, the sum of the `k` largest norms (Talagrand 1995, Eq. (13.5), p. 197). -/
noncomputable def topSum {W : Type*} [NormedAddCommGroup W] {N : ℕ}
    (x : Fin N → W) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 k, normRearr x i

/-- `Σ_{i ≤ k} ‖x_i‖*` for `k ∈ ℕ ∪ {∞}` (used with `k = k(x)`, Eq. (13.13), p. 199): the
index is capped at `N`, which does not change the sum; `k = ∞` gives the sum of all norms. -/
noncomputable def topSumE {W : Type*} [NormedAddCommGroup W] {N : ℕ}
    (x : Fin N → W) (k : ℕ∞) : ℝ :=
  topSum x (min k (N : ℕ∞)).toNat

/-- Talagrand (1995), Eq. (3.1.1), p. 113: for sets `A_1, …, A_q ⊆ Ω^N` and `x ∈ Ω^N`,
`f(A_1, …, A_q, x) = inf { card { i ≤ N ; x_i ∉ {y_i^1, …, y_i^q} } ; y^1 ∈ A_1, …, y^q ∈ A_q }`.
Valued in `ℕ∞`; the infimum over an empty choice is `⊤ = +∞`. -/
noncomputable def qPointDist {Ω : Type*} {N q : ℕ} (A : Fin q → Set (Fin N → Ω))
    (x : Fin N → Ω) : ℕ∞ :=
  ⨅ (y : Fin q → Fin N → Ω) (_ : ∀ l, y l ∈ A l),
    ((Finset.univ.filter (fun i => ∀ l, x i ≠ y l i)).card : ℕ∞)

/-- The set `B = { σ ≤ b } ⊆ W^N` (Talagrand 1995, p. 199), with `σ = √(σ²)`. -/
def sigmaBall {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {N : ℕ} (b : ℝ) :
    Set (Fin N → W) :=
  {y | Real.sqrt (sigmaSq y) ≤ b}

/-- `k(x) = f(B, …, B, x)` with `B = { σ ≤ b }` occurring `q` times (Talagrand 1995, p. 199). -/
noncomputable def kSigma {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {N : ℕ}
    (q : ℕ) (b : ℝ) (x : Fin N → W) : ℕ∞ :=
  qPointDist (fun _ : Fin q => sigmaBall b) x

end TalagrandConc.BanachSums
