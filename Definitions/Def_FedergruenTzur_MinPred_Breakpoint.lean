import Mathlib
import Definitions.Def_FedergruenTzur_MinPred_Model

/-!
# Federgruen–Tzur (1991), §1: the intercept `A(k, l)` of (4) and the root `G(k, l)` of (5)

A. Federgruen and M. Tzur, Management Science 37(8), 1991, pp. 913–914, eqs. (4), (5) and the
symmetric extension of `G` stated after Lemma 2.

* `A k l` is the first line of (4):
  `A(k, l) = F(k-1) + K_k - F(l-1) - K_l + S(k, l-1) + c_k [D(l-1) - D(k-1)] + D(l-1)(c_l - c_{k,l})`.
* `Gord k l` is (5) for an ordered pair `k < l`:
  `A(k, l) / (C̃(l) - C̃(k))` if `C̃(l) ≠ C̃(k)`, `+∞` if `C̃(l) = C̃(k)` and `A(k, l) ≤ 0`, and `−∞` if
  `C̃(l) = C̃(k)` and `A(k, l) > 0`.
* `G k l` is the symmetric extension `G(l, k) = G(k, l)` for `k < l`.

**Formalization Note.** Values live in `EReal`, so `+∞ = ⊤` and `−∞ = ⊥` are kept apart from every
real value. The diagonal value `G k k` (never used by the paper) is `Gord k k`.
-/

namespace FedergruenTzur.MinPred

namespace LotSizing

variable (P : LotSizing)

/-- `A(k, l)`, the first line of (4). -/
noncomputable def A (k l : ℕ) : ℝ :=
  P.Fopt (k - 1) + P.K k - P.Fopt (l - 1) - P.K l + P.S k (l - 1)
    + P.c k * (P.D (l - 1) - P.D (k - 1)) + P.D (l - 1) * (P.c l - P.cij k l)

/-- `G(k, l)` of (5) for an ordered pair `k < l`. -/
noncomputable def Gord (k l : ℕ) : EReal :=
  if P.Ctil l ≠ P.Ctil k then ((P.A k l / (P.Ctil l - P.Ctil k) : ℝ) : EReal)
  else if P.A k l ≤ 0 then ⊤ else ⊥

/-- `G(k, l)` extended symmetrically: `G(k, l)` of (5) when `k ≤ l`, and `G(l, k)` when `l < k`. -/
noncomputable def G (k l : ℕ) : EReal :=
  if k ≤ l then P.Gord k l else P.Gord l k

end LotSizing

end FedergruenTzur.MinPred
