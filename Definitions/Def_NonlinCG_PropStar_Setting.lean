import Mathlib
import Definitions.Def_NonlinCG_FRBound_Setting

namespace NonlinCG.PropStar

/-!
Gilbert & Nocedal, *Global convergence properties of conjugate gradient methods for
optimization*, INRIA Rapport de Recherche 1268 (June 1990), HAL inria-00075291v1, §1, §2 and §4,
pp. 2–4 and 11–14: the problem (1.1), the conjugate gradient iteration (1.2)–(1.3), the
Polak–Ribière scalar (1.5), Assumptions 2.1, the Wolfe conditions (2.4)–(2.5), the Zoutendijk
condition (2.7), the sufficient descent condition (4.1), Property (*) (4.10)–(4.12), the unit
directions `u_k := d_k/‖d_k‖` (Lemma 4.1) and the index sets `𝒦^λ_{k,Δ}` (p. 14).

Conventions: `E` is a finite-dimensional real inner product space (the "scalar product used to
compute the gradient", p. 2), and `gradient f` is the gradient for that product. Sequences are
indexed from `1` as in the paper; index `0` is never used.
-/

open Classical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The sufficient descent condition (4.1) with constant `σ₃`:
`⟨g_k, d_k⟩ ≤ −σ₃‖g_k‖²` for all `k ≥ 1`. -/
def SufficientDescent (f : E → ℝ) (σ₃ : ℝ) (x d : ℕ → E) : Prop :=
  ∀ k ≥ 1, inner ℝ (NonlinCG.FRBound.g f x k) (d k) ≤ -σ₃ * ‖NonlinCG.FRBound.g f x k‖ ^ 2

/-- Property (*) (p. 13, (4.10)–(4.12)): whenever `0 < γ ≤ ‖g_k‖ ≤ γ̄` for all `k ≥ 1` (4.10),
there are constants `b > 1` and `λ > 0` (allowed to depend on `γ, γ̄`) such that for all `k ≥ 2`
(where `β_k` and `s_{k−1} = x_k − x_{k−1}` exist), `|β_k| ≤ b` (4.11) and
`‖s_{k−1}‖ ≤ λ ⟹ |β_k| ≤ 1/(2b)` (4.12). If the run never satisfies (4.10) the property holds
vacuously, as in the paper ("Under this assumption we say …"). -/
def PropertyStar (f : E → ℝ) (β : ℕ → ℝ) (x : ℕ → E) : Prop :=
  ∀ γ γbar : ℝ, 0 < γ → (∀ k ≥ 1, γ ≤ ‖NonlinCG.FRBound.g f x k‖ ∧ ‖NonlinCG.FRBound.g f x k‖ ≤ γbar) →
    ∃ b > 1, ∃ lam > 0, ∀ k ≥ 2,
      |β k| ≤ b ∧ (‖x k - x (k - 1)‖ ≤ lam → |β k| ≤ 1 / (2 * b))

/-- The unit direction `u_k := d_k/‖d_k‖` (Lemma 4.1, p. 12). Meaningful only when `d_k ≠ 0`
(Lean returns `0` at `d_k = 0`). -/
noncomputable def u (d : ℕ → E) (k : ℕ) : E := ‖d k‖⁻¹ • d k

/-- `𝒦^λ_{k,Δ} := {i ∈ ℕ* : k ≤ i ≤ k + Δ − 1, ‖s_{i−1}‖ > λ}` (p. 14), the indices of a block of
`Δ` consecutive iterates whose preceding step `s_{i−1} = x_i − x_{i−1}` exceeds `λ`. As in
`𝒦^λ := {i ∈ ℕ* : i ≥ 2, ‖s_{i−1}‖ > λ}` only indices `i ≥ 2` are counted, since `s₀` does not
exist in the paper. Used with `Δ ≥ 1`. -/
noncomputable def Kset (lam : ℝ) (x : ℕ → E) (k Δ : ℕ) : Finset ℕ :=
  (Finset.Icc k (k + Δ - 1)).filter (fun i => 2 ≤ i ∧ lam < ‖x i - x (i - 1)‖)

end NonlinCG.PropStar
