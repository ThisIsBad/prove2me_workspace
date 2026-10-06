import Mathlib
import Definitions.Def_FedergruenTzur_MinPred_Breakpoint

/-!
# Federgruen–Tzur (1991), Theorem 1: ranked candidate lists, their `g`-values and condition (6)

A. Federgruen and M. Tzur, Management Science 37(8), 1991, §2, p. 915, Theorem 1.

A set `S = {i_1, …, i_r} ⊆ {1, …, j}` ranked as in Theorem 1 is a list `L = [i_1, …, i_r]`:
* `IsRanked j L`: the entries are distinct periods in `{1, …, j}` ordered by nonascending `C̃`-value,
  with equal `C̃`-values ranked in ascending order of period index, i.e. for every earlier entry `a`
  and later entry `b`: `C̃(b) < C̃(a)`, or `C̃(a) = C̃(b)` and `a < b`.
* `gval j L m` is the paper's `g(m + 1)` (Lean lists are 0-based, the paper is 1-based):
  `g(1) = D(j)` and `g(l) = G(i_l, i_{l-1})` for `l = 2, …, r`.
* `Cond6 j L` is condition (6): `g(1) < g(2) < ⋯ < g(r) < ∞`.

**Formalization Note.** `L.getD m 0` is the paper's `i_{m+1}`; out-of-range indices are never used
in `gval` for `m < L.length`. For the empty list `Cond6` reduces to `D(j) < ∞`, which is true.
-/

namespace FedergruenTzur.MinPred

namespace LotSizing

variable (P : LotSizing)

/-- `L` lists distinct periods of `{1, …, j}` in nonascending order of `C̃`, ties broken by
ascending period index. -/
def IsRanked (j : ℕ) (L : List ℕ) : Prop :=
  L.Nodup ∧ (∀ i ∈ L, 1 ≤ i ∧ i ≤ j) ∧
    L.Pairwise (fun a b => P.Ctil b < P.Ctil a ∨ (P.Ctil a = P.Ctil b ∧ a < b))

/-- The `g`-values of Theorem 1, 0-based: `gval j L 0 = D(j)` (the paper's `g(1)`) and, for
`m ≥ 1`, `gval j L m = G(i_{m+1}, i_m)` (the paper's `g(m + 1)`), with `i_{m+1} = L.getD m 0`. -/
noncomputable def gval (j : ℕ) (L : List ℕ) (m : ℕ) : EReal :=
  if m = 0 then ((P.D j : ℝ) : EReal) else P.G (L.getD m 0) (L.getD (m - 1) 0)

/-- Condition (6): `g(1) < g(2) < ⋯ < g(r) < ∞`. -/
def Cond6 (j : ℕ) (L : List ℕ) : Prop :=
  (∀ m, m + 1 < L.length → P.gval j L m < P.gval j L (m + 1)) ∧
    P.gval j L (L.length - 1) < ⊤

end LotSizing

end FedergruenTzur.MinPred
