import Mathlib

namespace LostSalesOldNew.StateReduction

open MeasureTheory

/-- One period of the lost-sales pipeline with no new order (p. 1257). From the vector
`(x_0, …, x_m)` and the demand `d` it returns the first `m` components of the next state,
`([x_0 − d]^+ + x_1, x_2, …, x_m)`. This is the paper's `x_+^{m−1}` of `x^m`. -/
noncomputable def shift {m : ℕ} (x : Fin (m + 1) → ℝ) (d : ℝ) : Fin m → ℝ :=
  fun i => if (i : ℕ) = 0 then max (x 0 - d) 0 + x i.succ else x i.succ

/-- The state transition of the system with lead time `L` (p. 1257):
`x_+ = ([x_0 − d]^+ + x_1, x_2, …, x_{L−1}, z)`. -/
noncomputable def next {L : ℕ} (x : Fin L → ℝ) (z d : ℝ) : Fin L → ℝ :=
  shift (Fin.snoc (α := fun _ => ℝ) x z) d

/-- A demand law (p. 1257: demands are independent, nonnegative and stationary): a probability law on
`[0, ∞)`. -/
structure IsDemand (D : Measure ℝ) : Prop where
  isProb : IsProbabilityMeasure D
  nonneg : D (Set.Iio 0) = 0

/-- `v_l = Σ_{m=l}^{L−1} x_m` for `l ≤ L − 1`, and `v_L = 0` (p. 1258). Defined for every `l : ℕ`;
it vanishes for `l ≥ L`. -/
def v {L : ℕ} (x : Fin L → ℝ) (l : ℕ) : ℝ :=
  ∑ m : Fin L, if l ≤ (m : ℕ) then x m else 0

/-- A level vector `s = (s_0, …, s_L)` with `s_0 ≥ s_1 ≥ ⋯ ≥ s_L ≥ 0` (p. 1259). -/
def IsLevelVector {L : ℕ} (s : Fin (L + 1) → ℝ) : Prop :=
  Antitone s ∧ 0 ≤ s (Fin.last L)

/-- `X(s) = {x ≥ 0 : v_l ≤ s_l, l = 0, …, L − 1}` (p. 1259). -/
def Xs {L : ℕ} (s : Fin (L + 1) → ℝ) : Set (Fin L → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∀ l : Fin L, v x l ≤ s l.castSucc}

/-- `Z(s)` (p. 1259): stationary policies `z` (an order `z(x) ≥ 0` in every state `x ≥ 0`) with
`z(x) = 0` for states `x ≥ 0` outside `X(s)`, and `v_l + z(x) ≤ s_l` for `l = 0, …, L` and
`x ∈ X(s)`. -/
def Zs {L : ℕ} (s : Fin (L + 1) → ℝ) : Set ((Fin L → ℝ) → ℝ) :=
  {z | (∀ x : Fin L → ℝ, (∀ i, 0 ≤ x i) → 0 ≤ z x) ∧
       (∀ x : Fin L → ℝ, (∀ i, 0 ≤ x i) → x ∉ Xs s → z x = 0) ∧
       (∀ x ∈ Xs s, ∀ l : Fin (L + 1), v x l + z x ≤ s l)}

/-- The vector base-stock policy with parameter `s`, (5) with `s` in place of `s̄` (p. 1258):
`z(x) = [min{s_l − v_l, l = 0, …, L}]^+`. -/
noncomputable def vectorBaseStock {L : ℕ} (s : Fin (L + 1) → ℝ) (x : Fin L → ℝ) : ℝ :=
  max (Finset.univ.inf' Finset.univ_nonempty (fun l : Fin (L + 1) => s l - v x l)) 0

/-- The state in period `t` under the stationary policy `z`, from the initial state `x`, along the
demand path `ds` (`ds t` is the demand of period `t`): `x_{t+1} = (x_t)_+` with order `z(x_t)`. -/
noncomputable def traj {L : ℕ} (z : (Fin L → ℝ) → ℝ) (x : Fin L → ℝ) (ds : ℕ → ℝ) :
    ℕ → (Fin L → ℝ)
  | 0 => x
  | t + 1 => next (traj z x ds t) (z (traj z x ds t)) (ds t)

end LostSalesOldNew.StateReduction
