import Mathlib

namespace BealeConvexMin.QuadSimplex

/-!
Beale (1955), §3, pp. 175–176, eqs. (3.3)–(3.6): the change of nonbasic variable in a quadratic
function `C = Σ_{k,l=0}^{N} c_kl z_k z_l` with `z_0 = 1` (eq. (3.1), `N = n - m`).

Slot convention: the nonbasic variables occupy the fixed slots `Fin (N+1)`, slot `0` holding the
constant `z_0 = 1`. A pivot at slot `p` removes the old `z_p` and puts the new nonbasic variable,
which the paper calls `z_q`, **into slot `p`**. Hence the paper's index `q` in (3.4)–(3.7) is
slot `p` after the pivot, and the paper's "`l ≠ q`", "`k ≠ q`" read "`l ≠ p`", "`k ≠ p`" here.
-/

/-- Eq. (3.4). If the new nonbasic variable is `z_q = d_0 + Σ_{l=1}^{N} d_l z_l` (eq. (3.3)), then
`z_p = e_0 + e_q z_q + Σ_{l ≠ p} e_l z_l` with `e_q = 1/d_p` and `e_l = -d_l/d_p` for `l ≠ p`
(including `l = 0`: `e_0 = -d_0/d_p`). Since `z_q` is stored in slot `p`, `e_q` is entry `p`. -/
noncomputable def pivotE {N : ℕ} (d : Fin (N + 1) → ℝ) (p : Fin (N + 1)) : Fin (N + 1) → ℝ :=
  fun l => if l = p then 1 / d p else -d l / d p

/-- Substitution of `z_p = Σ_l e_l z'_l` (with `z'_0 = 1`, and `z'_p` the new variable in slot `p`)
into the linear form `Σ_l v_l z_l`: the coefficient of the new slot `p` is `v_p e_p`, and every
other coefficient becomes `v_l + v_p e_l`. This is the rule (3.5) for one row, and the rule by
which "the transformed `a_kl` are derived from the old `a_hl`" (p. 176). -/
def substVec {N : ℕ} (v e : Fin (N + 1) → ℝ) (p : Fin (N + 1)) : Fin (N + 1) → ℝ :=
  fun l => if l = p then v p * e p else v l + v p * e l

/-- The new row of a restricted variable `x_h = Σ_l a_hl z_l` after the pivot at slot `p` defined by
the new nonbasic variable with coefficients `d` (eq. (3.3)). -/
noncomputable def pivotRow {N : ℕ} (r : Fin (N + 1) → ℝ) (p : Fin (N + 1))
    (d : Fin (N + 1) → ℝ) : Fin (N + 1) → ℝ :=
  substVec r (pivotE d p) p

/-- Eq. (3.5): `c'_kq = c_kp e_q` and `c'_kl = c_kl + c_kp e_l` for `l ≠ q` (with `q` = slot `p`):
the substitution of (3.4) for `z_p` inside the brackets, i.e. in every row of `(c_kl)`. -/
noncomputable def pivotCPrime {N : ℕ} (c : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (p : Fin (N + 1)) (d : Fin (N + 1) → ℝ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  Matrix.of fun k l =>
    if l = p then c k p * pivotE d p p else c k l + c k p * pivotE d p l

/-- Eq. (3.6): `c''_ql = c'_pl e_q` and `c''_kl = c'_kl + c'_pl e_k` for `k ≠ q` (with `q` = slot
`p`): the substitution of (3.4) for the remaining `z_p`, the one multiplying each bracket. The
matrix `(c''_kl)` is the transformed `(c_kl)` after the pivot at slot `p` with new nonbasic
variable (3.3) of coefficients `d`. -/
noncomputable def pivotC {N : ℕ} (c : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (p : Fin (N + 1)) (d : Fin (N + 1) → ℝ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  Matrix.of fun k l =>
    if k = p then pivotCPrime c p d p l * pivotE d p p
    else pivotCPrime c p d k l + pivotCPrime c p d p l * pivotE d p k

/-- The value `C = Σ_{k=0}^{N} Σ_{l=0}^{N} c_kl z_k z_l` of eq. (3.1) at the point `z`
(the caller sets `z 0 = 1`). -/
def quadValue {N : ℕ} (c : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (z : Fin (N + 1) → ℝ) : ℝ :=
  ∑ k, ∑ l, c k l * z k * z l

end BealeConvexMin.QuadSimplex
