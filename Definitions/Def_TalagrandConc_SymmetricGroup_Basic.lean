import Mathlib

namespace TalagrandConc.SymmetricGroup

open scoped ENNReal Classical
open Equiv

/-! Talagrand (1995), Chapter 5 "The Symmetric Group", pp. 145–149.
`S_N` is `Equiv.Perm (Fin N)` (0-based: the paper's `{1, …, N}` is `Fin N`, and in `S_{N+1}`
the paper's point `N + 1` is `Fin.last N`). Products of permutations are composition:
`(ρ * τ) ℓ = ρ (τ ℓ)`, so the paper's `ρ ∘ t_i` is `ρ * t_i`. -/

/-- Talagrand (1995), p. 145: for `A ⊆ S_N` and `σ ∈ S_N`,
`U_A(σ) = { s ∈ {0,1}^N ; ∃ τ ∈ A, ∀ ℓ ≤ N, s_ℓ = 0 ⇒ τ(ℓ) = σ(ℓ) }`,
viewed as a subset of `ℝ^N`. -/
def U {N : ℕ} (A : Set (Perm (Fin N))) (σ : Perm (Fin N)) : Set (Fin N → ℝ) :=
  {s | (∀ ℓ, s ℓ = 0 ∨ s ℓ = 1) ∧ ∃ τ ∈ A, ∀ ℓ, s ℓ = 0 → τ ℓ = σ ℓ}

/-- Talagrand (1995), p. 145: `V_A(σ)`, the convex hull of `U_A(σ)` (in `[0,1]^N ⊆ ℝ^N`). -/
def V {N : ℕ} (A : Set (Perm (Fin N))) (σ : Perm (Fin N)) : Set (Fin N → ℝ) :=
  convexHull ℝ (U A σ)

/-- Talagrand (1995), p. 145: `f(A, σ) = inf { Σ_{ℓ ≤ N} s_ℓ² ; s ∈ V_A(σ) }`
(the *squared* Euclidean distance from `0` to `V_A(σ)`), valued in `ℝ≥0∞`;
`f(∅, σ) = ⊤ = +∞`. -/
noncomputable def f {N : ℕ} (A : Set (Perm (Fin N))) (σ : Perm (Fin N)) : ℝ≥0∞ :=
  ⨅ s ∈ V A σ, ENNReal.ofReal (∑ ℓ, s ℓ ^ 2)

/-- Talagrand (1995), p. 145: for `p ≤ N`,
`f(A, σ, p) = inf { s_p² + Σ_{ℓ ≤ N} s_ℓ² ; s ∈ V_A(σ) }` (the coordinate `p` counts twice). -/
noncomputable def fp {N : ℕ} (A : Set (Perm (Fin N))) (σ : Perm (Fin N)) (p : Fin N) : ℝ≥0∞ :=
  ⨅ s ∈ V A σ, ENNReal.ofReal (s p ^ 2 + ∑ ℓ, s ℓ ^ 2)

/-- Talagrand (1995), Eq. (5.5), p. 146: for `p, m ≤ N`, `p ≠ m`,
`f(A, σ, p, m) = inf { s_p² + Σ_{ℓ ≤ N} s_ℓ² ; s ∈ V_A(σ), s_m = 0 }`.
The infimum of the empty set is `⊤ = +∞`. The paper defines it only for `p ≠ m`; every
statement using it carries that hypothesis. -/
noncomputable def fpm {N : ℕ} (A : Set (Perm (Fin N))) (σ : Perm (Fin N)) (p m : Fin N) :
    ℝ≥0∞ :=
  ⨅ s ∈ {s ∈ V A σ | s m = 0}, ENNReal.ofReal (s p ^ 2 + ∑ ℓ, s ℓ ^ 2)

/-- Talagrand (1995), Eq. (5.6), p. 146: for `i, j ≤ N`,
`g(A, σ, i, j) = inf { Σ_{ℓ ≠ i, j} s_ℓ² ; s ∈ V_A(σ) }`. -/
noncomputable def g {N : ℕ} (A : Set (Perm (Fin N))) (σ : Perm (Fin N)) (i j : Fin N) : ℝ≥0∞ :=
  ⨅ s ∈ V A σ, ENNReal.ofReal (∑ ℓ ∈ Finset.univ.filter (fun ℓ => ℓ ≠ i ∧ ℓ ≠ j), s ℓ ^ 2)

/-- The integrand `exp((1/16) z)` for `z ∈ [0, +∞]`, computed in `EReal`
(so `exp(+∞) = +∞`). -/
noncomputable def exp16 (z : ℝ≥0∞) : ℝ≥0∞ :=
  EReal.exp (((z / 16 : ℝ≥0∞)) : EReal)

/-- The integral `∫ F dQ` against the uniform probability `Q` on a finite set `S`:
`(1/|S|) Σ_{x ∈ S} F(x)`. -/
noncomputable def uniformAvg {α : Type*} (S : Finset α) (F : α → ℝ≥0∞) : ℝ≥0∞ :=
  ((S.card : ℝ≥0∞))⁻¹ * ∑ x ∈ S, F x

/-- The uniform probability `Q` on a finite set `S`, evaluated at a set `A`:
`Q(A) = |A ∩ S| / |S|`. -/
noncomputable def uniformProb {α : Type*} (S : Finset α) (A : Set α) : ℝ≥0∞ :=
  ((S.card : ℝ≥0∞))⁻¹ * ((S.filter (fun x => x ∈ A)).card : ℝ≥0∞)

/-- Talagrand (1995), p. 145: `P_N(A)`, the canonical (uniform) probability on `S_N`. -/
noncomputable def PN {N : ℕ} (A : Set (Perm (Fin N))) : ℝ≥0∞ :=
  uniformProb Finset.univ A

/-- Talagrand (1995), p. 146: `G_i = { σ ∈ S_{N+1} ; σ(i) = N + 1 }`; the uniform probability
on it is `Q_i` (p. 147). -/
def G (N : ℕ) (i : Fin (N + 1)) : Finset (Perm (Fin (N + 1))) :=
  Finset.univ.filter (fun σ => σ i = Fin.last N)

/-- Talagrand (1995), p. 149: `G'_i = { σ ∈ S_{N+1} ; σ(N + 1) = i }`; the uniform probability
on it is `Q'_i` (p. 149). -/
def G' (N : ℕ) (i : Fin (N + 1)) : Finset (Perm (Fin (N + 1))) :=
  Finset.univ.filter (fun σ => σ (Fin.last N) = i)

/-- Talagrand (1995), p. 147: `t_i = t_{N+1, i}`, the transposition of `N + 1` and `i`
(the identity when `i = N + 1`). -/
def t (N : ℕ) (i : Fin (N + 1)) : Perm (Fin (N + 1)) :=
  swap (Fin.last N) i

/-- A permutation `ρ ∈ S_{N+1}` fixing `N + 1` *restricts to* `τ ∈ S_N`: `ρ(ℓ) = τ(ℓ)` for all
`ℓ ≤ N`. This is how the paper "considers `S_N` as the permutations of `S_{N+1}` fixing
`N + 1`" (pp. 147, 149). -/
def Restricts {N : ℕ} (ρ : Perm (Fin (N + 1))) (τ : Perm (Fin N)) : Prop :=
  ∀ ℓ : Fin N, ρ ℓ.castSucc = (τ ℓ).castSucc

/-- Talagrand (1995), p. 147: `R(A_i) ⊆ S_N`, the image of `A_i = A ∩ G_i` under
`R : ρ ↦ ρ ∘ t_i` (which maps `G_i` into the permutations fixing `N + 1`, i.e. into `S_N`). -/
def RImage {N : ℕ} (A : Set (Perm (Fin (N + 1)))) (i : Fin (N + 1)) : Set (Perm (Fin N)) :=
  {τ | ∃ ρ ∈ A, ρ i = Fin.last N ∧ Restricts (ρ * t N i) τ}

/-- Talagrand (1995), p. 149: `R'(A'_i) ⊆ S_N`, the image of `A'_i = A ∩ G'_i` under
`R' : ρ ↦ t_i ∘ ρ` (which maps `G'_i` into the permutations fixing `N + 1`, i.e. into `S_N`). -/
def R'Image {N : ℕ} (A : Set (Perm (Fin (N + 1)))) (i : Fin (N + 1)) : Set (Perm (Fin N)) :=
  {τ | ∃ ρ ∈ A, ρ (Fin.last N) = i ∧ Restricts (t N i * ρ) τ}

/-- Talagrand (1995), p. 145, inequality `(5.3)_N` for every subset `A` of `S_N` and every
`p ≤ N`: `∫ exp((1/16) f(A, σ, p)) dP_N(σ) ≤ 1/P_N(A)`. Used as the induction hypothesis
in Corollary 5.5, Lemma 5.6 and Lemma 5.10. -/
def Ineq53 (N : ℕ) : Prop :=
  ∀ (A : Set (Perm (Fin N))) (p : Fin N),
    uniformAvg Finset.univ (fun σ => exp16 (fp A σ p)) ≤ (PN A)⁻¹

/-- Talagrand (1995), p. 145, inequality `(5.4)_N` for every subset `A` of `S_N` and every
`p ≤ N`: `∫ exp((1/16) f(A, σ, σ⁻¹(p))) dP_N(σ) ≤ 1/P_N(A)`. Used as the induction hypothesis
in Lemma 5.6, Corollary 5.9 and Lemma 5.10. -/
def Ineq54 (N : ℕ) : Prop :=
  ∀ (A : Set (Perm (Fin N))) (p : Fin N),
    uniformAvg Finset.univ (fun σ => exp16 (fp A σ (σ⁻¹ p))) ≤ (PN A)⁻¹

end TalagrandConc.SymmetricGroup
