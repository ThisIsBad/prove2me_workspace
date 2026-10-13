import Mathlib
import Definitions.Def_TopkisRation_Levels_Model

namespace TopkisRation.Myopic

open MeasureTheory Filter Topology

/-- Data of the single-procurement model of §1 (pp. 162–163). -/
structure Model (n : ℕ) where
  k : ℕ
  a : ℕ → ℝ
  p : ℕ → Fin n → ℝ
  h : ℕ → ℝ → ℝ
  v₁ : ℝ → ℝ
  v₂ : ℝ → ℝ
  c : ℝ → ℝ
  μ : ℕ → Measure (Fin n → ℝ)

variable {n : ℕ}

/-- Assumptions (A), (B), (C), nonnegative backlog multipliers and finite-mean demands. -/
structure Model.Standing (M : Model n) : Prop where
  a_nonneg : ∀ t ∈ Finset.Icc 1 M.k, 0 ≤ M.a t
  h_convex : ∀ t ∈ Finset.Icc 1 M.k, ConvexOn ℝ (Set.Ici 0) (M.h t)
  h_cont : ∀ t ∈ Finset.Icc 1 M.k, ContinuousOn (M.h t) (Set.Ici 0)
  v₁_convex : ConvexOn ℝ (Set.Ici 0) M.v₁
  v₁_cont : ContinuousOn M.v₁ (Set.Ici 0)
  v₂_convex : ConvexOn ℝ Set.univ M.v₂
  v₂_cont : Continuous M.v₂
  v₂_slope : ∃ L : ℝ, ∀ w, (L : EReal) ≤ TopkisRation.Levels.rightDeriv M.v₂ w
  p_nonneg : ∀ t ∈ Finset.Icc 1 M.k, ∀ j, 0 ≤ M.p t j
  p_mono : ∀ t ∈ Finset.Icc 1 M.k, Monotone (M.p t)
  μ_prob : ∀ t ∈ Finset.Icc 1 M.k, IsProbabilityMeasure (M.μ t)
  μ_nonneg : ∀ t ∈ Finset.Icc 1 M.k, ∀ᵐ x ∂(M.μ t), 0 ≤ x
  μ_mean : ∀ t ∈ Finset.Icc 1 M.k, ∀ j, Integrable (fun x : Fin n → ℝ => x j) (M.μ t)

/-- The bracket of (1), where remaining stock is `z - ∑ j, (B j - u j)`. -/
def Model.obj (M : Model n) (t : ℕ) (G : ℝ → (Fin n → ℝ) → ℝ) (z : ℝ)
    (B u : Fin n → ℝ) : ℝ :=
  M.p t ⬝ᵥ u + M.h t (z - ∑ j, (B j - u j)) +
    G (z - ∑ j, (B j - u j)) (M.a t • u)

/-- The right-hand side of (1) with `gₜ₋₁` replaced by `G`. -/
noncomputable def Model.stage (M : Model n) (t : ℕ) (G : ℝ → (Fin n → ℝ) → ℝ)
    (z : ℝ) (B : Fin n → ℝ) : ℝ :=
  sInf (M.obj t G z B '' TopkisRation.Levels.feasible z B)

/-- `g₀(z,b) = v₁(z) + v₂(z - 1·b)` and `gₜ(z,b) = E fₜ(z,b+dₜ)`. -/
noncomputable def Model.g (M : Model n) : ℕ → ℝ → (Fin n → ℝ) → ℝ
  | 0 => fun z b => M.v₁ z + M.v₂ (z - ∑ j, b j)
  | t + 1 => fun z b => ∫ x, M.stage (t + 1) (M.g t) z (b + x) ∂(M.μ (t + 1))

/-- `fₜ(z,B)` for `1 ≤ t`. -/
noncomputable def Model.f (M : Model n) (t : ℕ) (z : ℝ) (B : Fin n → ℝ) : ℝ :=
  M.stage t (M.g (t - 1)) z B

/-- The function whose smallest minimum is the rationing level. -/
noncomputable def Model.levelObj (M : Model n) (t : ℕ) (j : Fin n) (w : ℝ) : ℝ :=
  M.p t j * w + M.h t w + M.g (t - 1) w (M.a t • w • Pi.single j 1)

end TopkisRation.Myopic
