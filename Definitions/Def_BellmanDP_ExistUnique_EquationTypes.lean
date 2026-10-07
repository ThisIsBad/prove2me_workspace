import Mathlib
import Definitions.Def_BellmanDP_ExistUnique_SupEquation

namespace BellmanDP.ExistUnique

/-- Bellman, *Dynamic Programming*, Ch. IV, § 3, conditions (1a)–(1e), p. 119: the equation
`f(p) = Sup_q [g(p, q) + h(p, q) f(T(p, q))]` on `D ⊆ ℝ^N` (Euclidean norm) is of **Type One**
with constant `a`. -/
structure TypeOne {N : ℕ} {S : Type*} (D : Set (EuclideanSpace ℝ (Fin N)))
    (g h : EuclideanSpace ℝ (Fin N) → S → ℝ)
    (T : EuclideanSpace ℝ (Fin N) → S → EuclideanSpace ℝ (Fin N)) (a : ℝ) : Prop where
  /-- (1a) `D` contains the null vector `θ`. -/
  zero_mem : (0 : EuclideanSpace ℝ (Fin N)) ∈ D
  /-- (1a) `T(p, q) ∈ D` for all `p ∈ D`. -/
  mapsTo : ∀ p ∈ D, ∀ q : S, T p q ∈ D
  /-- (1a) `g` is uniformly bounded for all `q ∈ S` and all `p ∈ D` with `‖p‖ ≤ c₁`. -/
  g_bdd : ∀ c₁ : ℝ, ∃ M : ℝ, ∀ p ∈ D, ‖p‖ ≤ c₁ → ∀ q : S, |g p q| ≤ M
  /-- (1b) `g(θ, q) = 0` for all `q ∈ S`. -/
  g_zero : ∀ q : S, g 0 q = 0
  /-- (1c) `|h(p, q)| ≤ 1` for all `p ∈ D`, `q ∈ S`. -/
  h_le_one : ∀ p ∈ D, ∀ q : S, |h p q| ≤ 1
  /-- (1d) `0 ≤ a` (implicit in the book: see the Formalization Note). -/
  a_nonneg : 0 ≤ a
  /-- (1d) `a < 1`. -/
  a_lt_one : a < 1
  /-- (1d) `‖T(p, q)‖ ≤ a ‖p‖` for all `q ∈ S`, `p ∈ D`. -/
  T_le : ∀ p ∈ D, ∀ q : S, ‖T p q‖ ≤ a * ‖p‖
  /-- (1e) `Σ_{n=0}^∞ v(aⁿ c) < ∞`, `v(c) = Sup_{‖p‖ ≤ c} Sup_q |g(p, q)|`, for every `c ≥ 0`. -/
  summable_v : ∀ c : ℝ, 0 ≤ c → Summable (fun n : ℕ => radialSup D g (a ^ n * c))

/-- Bellman, *Dynamic Programming*, Ch. IV, § 4, conditions (1a)–(1c), p. 121: the equation
`f(p) = Sup_q [g(p, q) + h(p, q) f(T(p, q))]` on `D ⊆ ℝ^N` is of **Type Two**. -/
structure TypeTwo {N : ℕ} {S : Type*} (D : Set (EuclideanSpace ℝ (Fin N)))
    (g h : EuclideanSpace ℝ (Fin N) → S → ℝ)
    (T : EuclideanSpace ℝ (Fin N) → S → EuclideanSpace ℝ (Fin N)) : Prop where
  /-- (1c) `T(p, q) ∈ D` for all `p ∈ D` (required under both alternatives). -/
  mapsTo : ∀ p ∈ D, ∀ q : S, T p q ∈ D
  /-- (1a) `|g(p, q)|` is uniformly bounded for all `q ∈ S` and `‖p‖ ≤ c₁`, `p ∈ D`. -/
  g_bdd : ∀ c₁ : ℝ, ∃ M : ℝ, ∀ p ∈ D, ‖p‖ ≤ c₁ → ∀ q : S, |g p q| ≤ M
  /-- (1b) `|h(p, q)| ≤ a < 1` for all `q ∈ S`, uniformly in any region `‖p‖ ≤ c₁`, `p ∈ D`. -/
  h_contract : ∀ c₁ : ℝ, ∃ a : ℝ, a < 1 ∧ ∀ p ∈ D, ‖p‖ ≤ c₁ → ∀ q : S, |h p q| ≤ a
  /-- (1c) `‖T(p, q)‖ ≤ ‖p‖` for all `p`, or alternatively `D` is a bounded region. -/
  T_cond : (∀ p ∈ D, ∀ q : S, ‖T p q‖ ≤ ‖p‖) ∨ Bornology.IsBounded D

end BellmanDP.ExistUnique
