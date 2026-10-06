import Mathlib

/-!
# Federgruen–Tzur (1991), §1: the dynamic lot size model and the recursion (2)

A. Federgruen and M. Tzur, *A Simple Forward Algorithm to Solve General Dynamic Lot Sizing Models
with n Periods in O(n log n) or O(n) Time*, Management Science 37(8), 1991, §1, pp. 912–913.

The data of the model are the demands `d i`, setup costs `K i`, variable per unit order costs `c i`
and unit holding costs `h i` of the periods `i = 1, 2, …` (the values at index `0` are never used).
The auxiliary notation of p. 912 is
* `D i = ∑_{k=1}^{i} d k` (cumulative demand; `D 0 = 0`),
* `H i = ∑_{k=1}^{i} h k` (cumulative holding cost; `H 0 = 0`),
* `cij i j = c i + h i + ⋯ + h (j-1)` (the paper's `c_{ij} = c_i + h_{ij}`),
* `Ctil i = c i - H (i - 1)` (the paper's `C̃(i)`),
* `S i j = ∑_{r=i}^{j-1} h r * (D j - D r)` (zero-inventory carrying cost of an order in `i` covering
  the demands of `i, …, j`).

The costs are those of the zero-inventory recursion (2), p. 913, with `F(0) = 0` (Step 0 of the
Algorithm, p. 918):
* `Flast l t = Fopt (l - 1) + K l + S l t + c l * (D t - D (l - 1))` is `F(l, t)` of (2);
* `Fopt t = min_{1 ≤ l ≤ t} F(l, t)` for `t ≥ 1` and `Fopt 0 = 0`.

**Formalization Note.** `Fopt` is *defined* by the recursion (2). Its identification with the
minimum cost over all feasible policies is Lemma 1 of the paper (Wagner–Whitin), which is not
formalized here. The horizon `n` is not a parameter: every statement only uses periods `≤ t`.
No sign assumptions are imposed on the data.
-/

namespace FedergruenTzur.MinPred

/-- The data of the dynamic lot size model of §1 (p. 912): demand `d i`, setup cost `K i`,
variable per unit order cost `c i` and unit holding cost `h i` (end of period `i`), for periods
`i = 1, 2, …`. -/
structure LotSizing where
  d : ℕ → ℝ
  K : ℕ → ℝ
  c : ℕ → ℝ
  h : ℕ → ℝ

namespace LotSizing

variable (P : LotSizing)

/-- Cumulative demand `D(i) = ∑_{k=1}^{i} d_k`. -/
def D (i : ℕ) : ℝ := ∑ k ∈ Finset.Icc 1 i, P.d k

/-- Cumulative holding cost `H(i) = ∑_{k=1}^{i} h_k`. -/
def H (i : ℕ) : ℝ := ∑ k ∈ Finset.Icc 1 i, P.h k

/-- `c_{ij} = c_i + h_i + h_{i+1} + ⋯ + h_{j-1}`: cost of ordering a unit in `i` and carrying it
till `j`. -/
def cij (i j : ℕ) : ℝ := P.c i + ∑ r ∈ Finset.Ico i j, P.h r

/-- `C̃(i) = c_i - H(i - 1)`. -/
def Ctil (i : ℕ) : ℝ := P.c i - P.H (i - 1)

/-- `S(i, j) = ∑_{r=i}^{j-1} h_r (D(j) - D(r))`. -/
def S (i j : ℕ) : ℝ := ∑ r ∈ Finset.Ico i j, P.h r * (P.D j - P.D r)

/-- `F(t)`: `F(0) = 0` and, for `t ≥ 1`, `F(t) = min_{1 ≤ l ≤ t} F(l, t)` with `F(l, t)` given by
the recursion (2). -/
noncomputable def Fopt : ℕ → ℝ
  | 0 => 0
  | t + 1 => (Finset.Icc 1 (t + 1)).attach.inf' (by simp)
      (fun l => Fopt (l.1 - 1) + P.K l.1 + P.S l.1 (t + 1) + P.c l.1 * (P.D (t + 1) - P.D (l.1 - 1)))
decreasing_by
  have := (Finset.mem_Icc.mp l.2).2
  omega

/-- `F(l, t) = F(l - 1) + K_l + S(l, t) + c_l [D(t) - D(l - 1)]`, the recursion (2). -/
noncomputable def Flast (l t : ℕ) : ℝ :=
  P.Fopt (l - 1) + P.K l + P.S l t + P.c l * (P.D t - P.D (l - 1))

theorem Fopt_zero : P.Fopt 0 = 0 := by
  rw [Fopt]

theorem Fopt_succ (t : ℕ) :
    P.Fopt (t + 1) = (Finset.Icc 1 (t + 1)).inf' (by simp) (fun l => P.Flast l (t + 1)) := by
  rw [Fopt]
  apply le_antisymm
  · exact Finset.le_inf' _ _ fun l hl =>
      Finset.inf'_le (fun l : Finset.Icc 1 (t + 1) => P.Flast l.1 (t + 1)) (Finset.mem_attach _ ⟨l, hl⟩)
  · exact Finset.le_inf' _ _ fun l _ => Finset.inf'_le (fun l => P.Flast l (t + 1)) l.2

end LotSizing

end FedergruenTzur.MinPred
