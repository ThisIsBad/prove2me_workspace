import Mathlib

namespace TruncNewton.NegCurv

/-- The state `(p_i, r_i, d_i, δ_i)` of the TNCG minor iteration (Steps 1–4, p. 194). -/
structure CGState (n : ℕ) where
  p : EuclideanSpace ℝ (Fin n)
  r : EuclideanSpace ℝ (Fin n)
  d : EuclideanSpace ℝ (Fin n)
  δ : ℝ

/-- The conjugate gradient recursion of the minor iteration, without stopping tests.
Step 1 gives the state at `i = 0`; Steps 2–4 give the state at `i + 1`. The CG step lengths
`αᵢ, βᵢ` of the page are called `a, b` here. -/
noncomputable def cg {n : ℕ} (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) : ℕ → CGState n
  | 0 => ⟨0, -g, -g, inner ℝ (-g) (-g)⟩
  | i + 1 =>
    let s := cg H g i
    let q := H s.d
    let a := inner ℝ s.r s.r / inner ℝ s.d q
    let p' := s.p + a • s.d
    let r' := s.r - a • q
    let b := inner ℝ r' r' / inner ℝ s.r s.r
    ⟨p', r', r' + b • s.d, inner ℝ r' r' + b ^ 2 * s.δ⟩

/-- The curvature test (2.1) of Step 2 at minor iteration `i`: `dᵢᵀ H dᵢ ≤ ε δᵢ`. -/
def test21 {n : ℕ} (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (ε : ℝ) (i : ℕ) : Prop :=
  inner ℝ ((cg H g i).d) (H (cg H g i).d) ≤ ε * (cg H g i).δ

/-- The truncation test (2.2) of Step 3 at minor iteration `i`: `‖r_{i+1}‖ ≤ η ‖g‖`
(the page's `‖r_{i+1}‖/‖g‖ ≤ η`, in product form). -/
def test22 {n : ℕ} (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (η : ℝ) (i : ℕ) : Prop :=
  ‖(cg H g (i + 1)).r‖ ≤ η * ‖g‖

/-- The minor iteration reaches iteration `i` (no test fired before) and exits there through
the curvature test (2.1). -/
def ExitsVia21 {n : ℕ} (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (ε η : ℝ) (i : ℕ) : Prop :=
  (∀ j < i, ¬ test21 H g ε j ∧ ¬ test22 H g η j) ∧ test21 H g ε i

/-- The minor iteration reaches iteration `i`, passes the curvature test (2.1) there, and exits
through the truncation test (2.2). -/
def ExitsVia22 {n : ℕ} (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (ε η : ℝ) (i : ℕ) : Prop :=
  (∀ j < i, ¬ test21 H g ε j ∧ ¬ test22 H g η j) ∧ ¬ test21 H g ε i ∧ test22 H g η i

end TruncNewton.NegCurv
