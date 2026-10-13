import Mathlib

namespace TopkisRation.Levels

open MeasureTheory Filter Topology

/-- Data of the single-procurement model of §1 (pp. 162–163). -/
structure Model (n : ℕ) where
  k : ℕ                          -- number of intervals in the period
  a : ℕ → ℝ                      -- a_t: b_{t-1} = a_t u_t
  p : ℕ → Fin n → ℝ              -- penalty p_t^j
  h : ℕ → ℝ → ℝ                  -- holding cost h_t
  v₁ : ℝ → ℝ                     -- salvage cost v₁(z)
  v₂ : ℝ → ℝ                     -- salvage cost v₂(z − a₁ Σ u₁ⁱ)
  c : ℝ → ℝ                      -- ordering cost c(w), w ≥ 0, at the start of interval k
  μ : ℕ → Measure (Fin n → ℝ)    -- law of the demand vector d_t

/-- `D⁺f(x)`: the right derivative, extended-real valued (it is `⊥` where the right difference
quotients tend to −∞, which a convex function on [0, ∞) may do at 0). -/
noncomputable def rightDeriv (f : ℝ → ℝ) (x : ℝ) : EReal :=
  Filter.liminf (fun ε : ℝ => (((f (x + ε) - f x) / ε : ℝ) : EReal)) (𝓝[>] 0)

variable {n : ℕ}

/-- The standing assumptions of §1: (A), (B), (C), a_t ≥ 0, and the demand distributions
(probability laws on [0, ∞)ⁿ with finite means). -/
structure Model.Standing (M : Model n) : Prop where
  a_nonneg : ∀ t ∈ Finset.Icc 1 M.k, 0 ≤ M.a t
  h_convex : ∀ t ∈ Finset.Icc 1 M.k, ConvexOn ℝ (Set.Ici 0) (M.h t)          -- (A)
  h_cont : ∀ t ∈ Finset.Icc 1 M.k, ContinuousOn (M.h t) (Set.Ici 0)          -- (A)
  v₁_convex : ConvexOn ℝ (Set.Ici 0) M.v₁                                     -- (B)
  v₁_cont : ContinuousOn M.v₁ (Set.Ici 0)                                     -- (B)
  v₂_convex : ConvexOn ℝ Set.univ M.v₂                                        -- (B)
  v₂_cont : Continuous M.v₂                                                   -- (B)
  v₂_slope : ∃ L : ℝ, ∀ w, (L : EReal) ≤ rightDeriv M.v₂ w                    -- (B)
  p_nonneg : ∀ t ∈ Finset.Icc 1 M.k, ∀ j, 0 ≤ M.p t j                         -- (C)
  p_mono : ∀ t ∈ Finset.Icc 1 M.k, Monotone (M.p t)                           -- (C)
  μ_prob : ∀ t ∈ Finset.Icc 1 M.k, IsProbabilityMeasure (M.μ t)
  μ_nonneg : ∀ t ∈ Finset.Icc 1 M.k, ∀ᵐ x ∂(M.μ t), 0 ≤ x
  μ_mean : ∀ t ∈ Finset.Icc 1 M.k, ∀ j, Integrable (fun x : Fin n → ℝ => x j) (M.μ t)

/-- Feasible unsatisfied-demand vectors in (1): 0 ≤ u ≤ B and w = z − 1·(B − u) ≥ 0. -/
def feasible (z : ℝ) (B : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {u | 0 ≤ u ∧ u ≤ B ∧ ∑ j, (B j - u j) ≤ z}

/-- The bracket of (1): p_t·u + h_t(w) + G(w, a_t u) with w = z − 1·(B − u). -/
def Model.obj (M : Model n) (t : ℕ) (G : ℝ → (Fin n → ℝ) → ℝ) (z : ℝ) (B u : Fin n → ℝ) : ℝ :=
  M.p t ⬝ᵥ u + M.h t (z - ∑ j, (B j - u j)) + G (z - ∑ j, (B j - u j)) (M.a t • u)

/-- The right-hand side of (1) with g_{t−1} replaced by `G`. -/
noncomputable def Model.stage (M : Model n) (t : ℕ) (G : ℝ → (Fin n → ℝ) → ℝ)
    (z : ℝ) (B : Fin n → ℝ) : ℝ :=
  sInf (M.obj t G z B '' feasible z B)

/-- g_0(z, b) = v₁(z) + v₂(z − 1·b) and g_t(z, b) = E f_t(z, b + d_t). -/
noncomputable def Model.g (M : Model n) : ℕ → ℝ → (Fin n → ℝ) → ℝ
  | 0 => fun z b => M.v₁ z + M.v₂ (z - ∑ j, b j)
  | t + 1 => fun z b => ∫ x, M.stage (t + 1) (M.g t) z (b + x) ∂(M.μ (t + 1))

/-- f_t(z, B), for 1 ≤ t (at t = 0 it is junk and never used). -/
noncomputable def Model.f (M : Model n) (t : ℕ) (z : ℝ) (B : Fin n → ℝ) : ℝ :=
  M.stage t (M.g (t - 1)) z B

/-- B^{(j)} = Σ_{i ≥ j} B^i. -/
def tailSum (B : Fin n → ℝ) (j : Fin n) : ℝ := ∑ i ∈ Finset.Ici j, B i

/-- The rationing level policy (7): u^j = (B^{(j)} − z + z̄^j)⁺ ∧ B^j, and u^j = B^j when z̄^j = +∞. -/
def rationU (zbar : Fin n → WithTop ℝ) (z : ℝ) (B : Fin n → ℝ) : Fin n → ℝ :=
  fun j => WithTop.untopD (B j) ((zbar j).map fun x => min (max (tailSum B j - z + x) 0) (B j))

/-- The function whose smallest minimum is z̄_t^j: p_t^j w + h_t(w) + g_{t−1}(w, a_t w δ_j). -/
noncomputable def Model.levelObj (M : Model n) (t : ℕ) (j : Fin n) (w : ℝ) : ℝ :=
  M.p t j * w + M.h t w + M.g (t - 1) w (M.a t • w • Pi.single j 1)

/-- "z̄ = +∞ if φ is strictly decreasing on [0, ∞), and z̄ is the smallest minimum of φ on [0, ∞)
otherwise." -/
def IsCriticalLevel (φ : ℝ → ℝ) (zbar : WithTop ℝ) : Prop :=
  (zbar = ⊤ ∧ StrictAntiOn φ (Set.Ici 0)) ∨
  ∃ x : ℝ, zbar = x ∧ 0 ≤ x ∧ (∀ y, 0 ≤ y → φ x ≤ φ y) ∧
    ∀ y, 0 ≤ y → (∀ w, 0 ≤ w → φ y ≤ φ w) → x ≤ y

end TopkisRation.Levels
