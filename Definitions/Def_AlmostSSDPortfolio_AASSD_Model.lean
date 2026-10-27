import Mathlib

namespace AlmostSSDPortfolio.AASSD

open MeasureTheory Set

/-- First-order lower partial moment of a finite discrete distribution with values `v` and
probabilities `p` (p. 7): `z ↦ Σ_t p_t (z − v_t) I(v_t ≤ z) = Σ_t p_t (z − v_t)⁺`. -/
noncomputable def lpm {T : Type*} [Fintype T] (p v : T → ℝ) (z : ℝ) : ℝ :=
  ∑ t, p t * max (z - v t) 0

/-- Expected value `Σ_t p_t v_t` of a finite discrete distribution. -/
def mean {T : Type*} [Fintype T] (p v : T → ℝ) : ℝ := ∑ t, p t * v t

/-- Variance `Σ_t p_t (v_t − E)²` of a finite discrete distribution. -/
def var {T : Type*} [Fintype T] (p v : T → ℝ) : ℝ := ∑ t, p t * (v t - mean p v) ^ 2

/-- A probability vector: nonnegative entries summing to `1` (Mathlib's standard simplex). -/
def IsProbVec {T : Type*} [Fintype T] (p : T → ℝ) : Prop := p ∈ stdSimplex ℝ T

/-- §2, pp. 6–7: `n` base assets with returns `x i t` in `T` scenarios of probability `p t`;
a benchmark portfolio with `Tb` scenarios of probability `q t'` and returns `bv t'`;
the investment return range `[a, b]`. -/
structure Setting (n T Tb : ℕ) where
  a : ℝ
  b : ℝ
  p : Fin T → ℝ
  x : Fin n → Fin T → ℝ
  q : Fin Tb → ℝ
  bv : Fin Tb → ℝ

variable {n T Tb : ℕ}

/-- Standing assumptions of §2 (p. 6–7) and §3.1 (p. 8): `−∞ < a < b < ∞`, both scenario
distributions are probability vectors, and every asset and benchmark return lies in `[a, b]`. -/
def Setting.Standing (S : Setting n T Tb) : Prop :=
  S.a < S.b ∧ IsProbVec S.p ∧ IsProbVec S.q ∧
    (∀ i t, S.x i t ∈ Icc S.a S.b) ∧ ∀ t', S.bv t' ∈ Icc S.a S.b

/-- The portfolio set `Λ = {λ ∈ ℝⁿ : Σ_i λ_i = 1, λ_i ≥ 0}`, p. 6. -/
def simplex (n : ℕ) : Set (Fin n → ℝ) := stdSimplex ℝ (Fin n)

/-- Return of portfolio `λ` in scenario `t`: `Σ_i x_{i,t} λ_i`, p. 6. -/
def Setting.ret (S : Setting n T Tb) (lam : Fin n → ℝ) (t : Fin T) : ℝ := ∑ i, S.x i t * lam i

/-- `F_λ^{(2)}`, the first-order LPM of the portfolio return, p. 7. -/
noncomputable def Setting.F2 (S : Setting n T Tb) (lam : Fin n → ℝ) : ℝ → ℝ :=
  lpm S.p (S.ret lam)

/-- `G^{(2)}`, the first-order LPM of the benchmark, p. 7. -/
noncomputable def Setting.G2 (S : Setting n T Tb) : ℝ → ℝ := lpm S.q S.bv

/-- `S₂ = {t ∈ [a, b] : F^{(2)}(t) > G^{(2)}(t)}`, §3.1, p. 8. -/
def Setting.S2 (S : Setting n T Tb) (lam : Fin n → ℝ) : Set ℝ :=
  {t | t ∈ Icc S.a S.b ∧ S.G2 t < S.F2 lam t}

/-- `S̄₂`, the complement of `S₂` taken inside `[a, b]`. -/
def Setting.S2c (S : Setting n T Tb) (lam : Fin n → ℝ) : Set ℝ :=
  {t | t ∈ Icc S.a S.b ∧ S.F2 lam t ≤ S.G2 t}

/-- Definition 1 (τ-ASSD), p. 8, for the portfolio return and the benchmark, with the ratio
cross-multiplied: `τ ∫_{S₂} (F^{(2)} − G^{(2)}) ≤ ∫_{S̄₂} (G^{(2)} − F^{(2)})` and `E X ≥ E Y`. -/
def Setting.IsASSD (S : Setting n T Tb) (lam : Fin n → ℝ) (τ : ℝ) : Prop :=
  τ * (∫ t in S.S2 lam, (S.F2 lam t - S.G2 t)) ≤ ∫ t in S.S2c lam, (S.G2 t - S.F2 lam t) ∧
    mean S.q S.bv ≤ mean S.p (S.ret lam)

/-- A discretization scheme, p. 9: grid points `d 0 < d 1 < … < d K` (the paper's
`d_1 < … < d_{T_D}`, `T_D = K + 1`) with `d 0 = a`, `d K = b`, containing every benchmark
return `b_{t'}`. -/
structure Discretization (S : Setting n T Tb) where
  K : ℕ
  d : Fin (K + 1) → ℝ
  strictMono : StrictMono d
  first : d 0 = S.a
  last : d (Fin.last K) = S.b
  covers : ∀ t', ∃ s, d s = S.bv t'

/-- The four cases of Definition 2 on one sub-interval `[dl, dr]`, with `fl, fr` the values of
`F_λ^{(2)}` and `gl, gr` those of `G^{(2)}` at its left and right end points. -/
noncomputable def violation (fl fr gl gr dl dr : ℝ) : ℝ :=
  if fl ≤ gl ∧ fr ≤ gr then 0
  else if fl ≤ gl ∧ gr ≤ fr then (dr - dl) * (fr - gr) ^ 2 / (2 * (fr - gr + gl - fl))
  else if gl ≤ fl ∧ fr ≤ gr then (dr - dl) * (fl - gl) ^ 2 / (2 * (gr - fr + fl - gl))
  else (fr + fl) * ((dr - dl) / 2) - (gr + gl) * ((dr - dl) / 2)

/-- `A_{D,s,λ}`, the approximate SSD violation on the sub-interval `[d s, d (s+1)]`,
Definition 2, p. 9. -/
noncomputable def Discretization.A {S : Setting n T Tb} (D : Discretization S)
    (lam : Fin n → ℝ) (s : Fin D.K) : ℝ :=
  violation (S.F2 lam (D.d s.castSucc)) (S.F2 lam (D.d s.succ)) (S.G2 (D.d s.castSucc))
    (S.G2 (D.d s.succ)) (D.d s.castSucc) (D.d s.succ)

/-- `F̂^{(2)}_{D,λ}`, the linear interpolation (2), p. 9, of `F_λ^{(2)}` at the grid points;
outside `[a, b]` it is `F_λ^{(2)}` itself. -/
noncomputable def Discretization.hatF2 {S : Setting n T Tb} (D : Discretization S)
    (lam : Fin n → ℝ) (z : ℝ) : ℝ :=
  if h : ∃ s : Fin D.K, z ∈ Icc (D.d s.castSucc) (D.d s.succ) then
    S.F2 lam (D.d h.choose.castSucc) +
      (S.F2 lam (D.d h.choose.succ) - S.F2 lam (D.d h.choose.castSucc)) /
        (D.d h.choose.succ - D.d h.choose.castSucc) * (z - D.d h.choose.castSucc)
  else S.F2 lam z

/-- `Ŝ₂ = {t ∈ [a, b] : F̂^{(2)}_{D,λ}(t) > G^{(2)}(t)}`, Proposition 3, p. 11. -/
def Discretization.hatS2 {S : Setting n T Tb} (D : Discretization S) (lam : Fin n → ℝ) :
    Set ℝ :=
  {t | t ∈ Icc S.a S.b ∧ S.G2 t < D.hatF2 lam t}

/-- Definition 3 (τ-AASSD), pp. 11–12, in the paper's cross-multiplied form (5d), p. 17:
`2(τ − 1) Σ_s A_{D,s,λ} ≤ Var Y + (b − E Y)² − Var X − (b − E X)²` and `E X ≥ E Y`. -/
def Discretization.IsAASSD {S : Setting n T Tb} (D : Discretization S) (lam : Fin n → ℝ)
    (τ : ℝ) : Prop :=
  2 * (τ - 1) * ∑ s, D.A lam s ≤
      var S.q S.bv + (S.b - mean S.q S.bv) ^ 2 - var S.p (S.ret lam) -
        (S.b - mean S.p (S.ret lam)) ^ 2 ∧
    mean S.q S.bv ≤ mean S.p (S.ret lam)

end AlmostSSDPortfolio.AASSD
