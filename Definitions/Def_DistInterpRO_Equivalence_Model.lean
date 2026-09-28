import Mathlib

open MeasureTheory

namespace DistInterpRO.Equivalence

/-- The distribution set `𝒫ₙ` of Theorem 2.1 (Xu–Caramanis–Mannor 2012, p. 96):
the Borel probability measures `μ` on `ℝᵐ` such that, for **every** index set
`S ⊆ [1 : n]` (`S = ∅` and `S = [1 : n]` included), `μ(⋃_{i ∈ S} 𝒵ᵢ) ≥ ∑_{i ∈ S} cᵢ`.
Indices are `Fin n = {0, …, n-1}`. -/
def distSet {m n : ℕ} (c : Fin n → ℝ) (Z : Fin n → Set (Fin m → ℝ)) :
    Set (Measure (Fin m → ℝ)) :=
  {μ | IsProbabilityMeasure μ ∧
    ∀ S : Finset (Fin n), ENNReal.ofReal (∑ i ∈ S, c i) ≤ μ (⋃ i ∈ S, Z i)}

/-- The extended-real expectation `∫ f dμ = ∫ f⁺ dμ − ∫ f⁻ dμ ∈ [−∞, +∞]`, computed with
lower Lebesgue integrals of the positive and negative parts (no Bochner integral).
By the `EReal` convention `⊤ - ⊤ = ⊥`, it is `⊥` when both parts are infinite. -/
noncomputable def expect {m : ℕ} (μ : Measure (Fin m → ℝ)) (f : (Fin m → ℝ) → ℝ) : EReal :=
  ((∫⁻ x, ENNReal.ofReal (f x) ∂μ : ENNReal) : EReal) -
    ((∫⁻ x, ENNReal.ofReal (-f x) ∂μ : ENNReal) : EReal)

open Classical in
/-- Dual feasibility for the semi-infinite dual LP in the proof of Theorem 2.1 (p. 97):
`α ∈ ℝ^{2ⁿ}` (indexed by subsets `S ⊆ N = [1 : n]`) is dual feasible if
`∑_S α_S 𝟏(x ∈ 𝒵_S) ≤ f(x)` for all `x ∈ 𝒵_N` and `α_S ≥ 0` for all `S ≠ N`,
where `𝒵_S = ⋃_{i ∈ S} 𝒵ᵢ`. The coordinate `α_N` is unsigned. -/
def IsDualFeasible {m n : ℕ} (Z : Fin n → Set (Fin m → ℝ)) (f : (Fin m → ℝ) → ℝ)
    (α : Finset (Fin n) → ℝ) : Prop :=
  (∀ x ∈ ⋃ i, Z i,
      ∑ S : Finset (Fin n), α S * (if x ∈ ⋃ i ∈ S, Z i then (1 : ℝ) else 0) ≤ f x) ∧
    ∀ S : Finset (Fin n), S ≠ Finset.univ → 0 ≤ α S

/-- The nested dual solution of the proof of Theorem 2.1 (p. 97), built from the values
`fᵢ` (`fi i`): `α_S = 0` except on the `n` nested sets `{1, …, i}` (here `Finset.Iic i`,
0-based), where `α_{{1,…,i}} = fᵢ − fᵢ₊₁` for `i < n` and `α_N = fₙ`
(0-based: the last index `n-1` has no successor, and its term is `f_{n-1} − 0`). -/
noncomputable def nestedDual {n : ℕ} (fi : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  ∑ i : Fin n,
    if S = Finset.Iic i then
      fi i - (if h : i.val + 1 < n then fi ⟨i.val + 1, h⟩ else 0)
    else 0

end DistInterpRO.Equivalence
