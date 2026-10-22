import Mathlib

open MeasureTheory ProbabilityTheory

namespace RetailVariety.Structure

/-- The most-popular sets `A_i = {1, …, i}` (§3.1, p. 1503). Variant `j` of the paper is
`⟨j - 1, _⟩ : Fin n`, so `A_i` is the set of indices with `val < i`; `A_0 = ∅`, `A_n = N`. -/
def popularSet (n i : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun j : Fin n => j.val < i)

/-- MNL choice probability (1), p. 1499: `q_j(S) = v_j / (∑_{i ∈ S} v_i + v_0)`.
The no-purchase preference `v0` is a separate real number, not a variant. -/
noncomputable def share {n : ℕ} (v : Fin n → ℝ) (v0 : ℝ) (S : Finset (Fin n)) (j : Fin n) : ℝ :=
  v j / (∑ i ∈ S, v i + v0)

/-- The critical fractile `z = Φ⁻¹(1 - c/p)` of (6), p. 1502, with `Φ` the standard normal
c.d.f.; written as the least `x` with `Φ(x) ≥ 1 - c/p`. -/
noncomputable def criticalFractile (p c : ℝ) : ℝ :=
  sInf {x : ℝ | 1 - c / p ≤ cdf (gaussianReal 0 1) x}

/-- Independent-population store profit (7), p. 1502:
`π_I(S, v) = (p - c) λ ∑_{j∈S} q_j - (p σ λ^β e^{-z²/2} / √(2π)) ∑_{j∈S} q_j^β`. -/
noncomputable def profitI {n : ℕ} (p c lam σ β : ℝ) (v : Fin n → ℝ) (v0 : ℝ)
    (S : Finset (Fin n)) : ℝ :=
  (p - c) * lam * ∑ j ∈ S, share v v0 S j
    - (p * σ * lam ^ β * Real.exp (-(criticalFractile p c) ^ 2 / 2) / Real.sqrt (2 * Real.pi))
      * ∑ j ∈ S, share v v0 S j ^ β

/-- Trend-following store profit (8), p. 1502: `π_T(S, v) = ∑_{j∈S} (p q_j - c)⁺ λ`. -/
noncomputable def profitT {n : ℕ} (p c lam : ℝ) (v : Fin n → ℝ) (v0 : ℝ)
    (S : Finset (Fin n)) : ℝ :=
  ∑ j ∈ S, max (p * share v v0 S j - c) 0 * lam

/-- `f(δ) = ∑_{j∈S} v_j + δ + v_0`, (9), p. 1503. -/
noncomputable def fDen {n : ℕ} (v : Fin n → ℝ) (v0 : ℝ) (S : Finset (Fin n)) (δ : ℝ) : ℝ :=
  ∑ j ∈ S, v j + δ + v0

/-- `g_I(δ)` of (10), p. 1503:
`(p - c) λ (∑_{j∈S} v_j + δ) - (p σ λ^β e^{-z²/2}/√(2π)) (∑_{j∈S} v_j^β + δ^β) f(δ)^{1-β}`. -/
noncomputable def gI {n : ℕ} (p c lam σ β : ℝ) (v : Fin n → ℝ) (v0 : ℝ) (S : Finset (Fin n))
    (δ : ℝ) : ℝ :=
  (p - c) * lam * (∑ j ∈ S, v j + δ)
    - (p * σ * lam ^ β * Real.exp (-(criticalFractile p c) ^ 2 / 2) / Real.sqrt (2 * Real.pi))
      * (∑ j ∈ S, v j ^ β + δ ^ β) * fDen v v0 S δ ^ (1 - β)

/-- `g_T(δ)` of (11), p. 1503, with `λ` multiplying both terms:
`λ [∑_{j∈S} (p v_j - c f(δ))⁺ + (p δ - c f(δ))⁺]`. (As printed, `λ` multiplies only the sum.) -/
noncomputable def gT {n : ℕ} (p c lam : ℝ) (v : Fin n → ℝ) (v0 : ℝ) (S : Finset (Fin n))
    (δ : ℝ) : ℝ :=
  lam * (∑ j ∈ S, max (p * v j - c * fDen v v0 S δ) 0 + max (p * δ - c * fDen v v0 S δ) 0)

/-- `h_I(δ) = g_I(δ) / f(δ)` (Lemma 1, p. 1503). -/
noncomputable def hI {n : ℕ} (p c lam σ β : ℝ) (v : Fin n → ℝ) (v0 : ℝ) (S : Finset (Fin n))
    (δ : ℝ) : ℝ :=
  gI p c lam σ β v v0 S δ / fDen v v0 S δ

/-- `h_T(δ) = g_T(δ) / f(δ)` (Lemma 1, p. 1503). -/
noncomputable def hT {n : ℕ} (p c lam : ℝ) (v : Fin n → ℝ) (v0 : ℝ) (S : Finset (Fin n))
    (δ : ℝ) : ℝ :=
  gT p c lam v v0 S δ / fDen v v0 S δ

end RetailVariety.Structure
