import Mathlib

namespace FedergruenZhengRQ.OPT

/-- `−G` is unimodal: `G` is nonincreasing up to some integer `m` and nondecreasing from `m` on.
Plateaus (equal consecutive values) are allowed. -/
def NegUnimodal (G : ℤ → ℝ) : Prop :=
  ∃ m : ℤ, AntitoneOn G (Set.Iic m) ∧ MonotoneOn G (Set.Ici m)

/-- `lim_{|y| → ∞} G(y) = ∞`: `G(y) → +∞` both as `y → −∞` and as `y → +∞`. -/
def Coercive (G : ℤ → ℝ) : Prop :=
  Filter.Tendsto G Filter.atBot Filter.atTop ∧ Filter.Tendsto G Filter.atTop Filter.atTop

/-- The long-run average cost (1) of the `(r, Q)` policy:
`C(r, Q) = [κ + ∑_{y = r+1}^{r+Q} G(y)] / Q`. Only meaningful for `Q ≥ 1`
(Lean's `x / 0 = 0` makes `cost κ G r 0 = 0`). -/
noncomputable def cost (κ : ℝ) (G : ℤ → ℝ) (r : ℤ) (Q : ℕ) : ℝ :=
  (κ + ∑ y ∈ Finset.Ioc r (r + (Q : ℤ)), G y) / (Q : ℝ)

/-- The window recursion of §2: `window G y₁ n = (L(n+1), R(n+1))`. It starts at `(y₁, y₁)` and
extends to the left when `G(L − 1) ≤ G(R + 1)` (ties go left), otherwise to the right. -/
noncomputable def window (G : ℤ → ℝ) (y₁ : ℤ) : ℕ → ℤ × ℤ
  | 0 => (y₁, y₁)
  | n + 1 =>
    if G ((window G y₁ n).1 - 1) ≤ G ((window G y₁ n).2 + 1) then
      ((window G y₁ n).1 - 1, (window G y₁ n).2)
    else
      ((window G y₁ n).1, (window G y₁ n).2 + 1)

/-- `L(Q)`, the left end of the window after `Q ≥ 1` points (`L 0` is a junk value, equal to `L 1`). -/
noncomputable def L (G : ℤ → ℝ) (y₁ : ℤ) (Q : ℕ) : ℤ := (window G y₁ (Q - 1)).1

/-- `R(Q)`, the right end of the window after `Q ≥ 1` points (`R 0` is a junk value, equal to `R 1`). -/
noncomputable def R (G : ℤ → ℝ) (y₁ : ℤ) (Q : ℕ) : ℤ := (window G y₁ (Q - 1)).2

/-- The sequence `y_1, y_2, …` of §2, 1-based: `y_1 = y₁` and
`y_{Q+1} = L(Q) − 1` if `G(L(Q) − 1) ≤ G(R(Q) + 1)`, else `R(Q) + 1`.
`y 0` is a junk value (set to `y₁`) and is never used. -/
noncomputable def y (G : ℤ → ℝ) (y₁ : ℤ) : ℕ → ℤ
  | 0 => y₁
  | 1 => y₁
  | Q + 2 =>
    if G (L G y₁ (Q + 1) - 1) ≤ G (R G y₁ (Q + 1) + 1) then L G y₁ (Q + 1) - 1
    else R G y₁ (Q + 1) + 1

/-- `C*(Q) = [κ + ∑_{i=1}^{Q} G(y_i)] / Q`, the page's formula (meaningful for `Q ≥ 1`). -/
noncomputable def Cstar (κ : ℝ) (G : ℤ → ℝ) (y₁ : ℤ) (Q : ℕ) : ℝ :=
  (κ + ∑ i ∈ Finset.Icc 1 Q, G (y G y₁ i)) / (Q : ℝ)

/-- The variables of Algorithm OPT: `S`, `Q`, `C*` (here `Cst`), `r` and `R`. -/
structure OPTState where
  S : ℝ
  Q : ℕ
  Cst : ℝ
  r : ℤ
  R : ℤ

/-- The state at the end of Step 0 when Step 0 has located the minimizer `L = y₁`:
`S := κ + G(L), Q := 1, C* := S, r := L − 1, R := L + 1`. -/
noncomputable def optInit (κ : ℝ) (G : ℤ → ℝ) (y₁ : ℤ) : OPTState :=
  ⟨κ + G y₁, 1, κ + G y₁, y₁ - 1, y₁ + 1⟩

/-- One pass of the `Repeat` body of Step 1. `Sum.inl (r, Q)` means "stop" with output `(r, Q)`;
`Sum.inr s'` is the state for the next pass. `G` is evaluated directly (the `ΔG` bookkeeping of the
page only computes `G(r)` and `G(R + 1)`). -/
noncomputable def optStep (G : ℤ → ℝ) (s : OPTState) : (ℤ × ℕ) ⊕ OPTState :=
  if G s.r ≤ G s.R then
    if s.Cst ≤ G s.r then Sum.inl (s.r, s.Q)
    else Sum.inr ⟨s.S + G s.r, s.Q + 1, (s.S + G s.r) / ((s.Q + 1 : ℕ) : ℝ), s.r - 1, s.R⟩
  else
    if s.Cst ≤ G s.R then Sum.inl (s.r, s.Q)
    else Sum.inr ⟨s.S + G s.R, s.Q + 1, (s.S + G s.R) / ((s.Q + 1 : ℕ) : ℝ), s.r, s.R + 1⟩

/-- Iterate Step 1 from a state with at most `n` passes; `none` if the fuel runs out first. -/
noncomputable def optLoop (G : ℤ → ℝ) : ℕ → OPTState → Option (ℤ × ℕ)
  | 0, _ => none
  | n + 1, s =>
    match optStep G s with
    | Sum.inl out => some out
    | Sum.inr s' => optLoop G n s'

/-- Algorithm OPT (Step 1 started from the minimizer `y₁`) with fuel `n`: `some (r, Q)` if it
stops within `n` passes with output `(r, Q)`, `none` otherwise. -/
noncomputable def optRun (κ : ℝ) (G : ℤ → ℝ) (y₁ : ℤ) (n : ℕ) : Option (ℤ × ℕ) :=
  optLoop G n (optInit κ G y₁)

/-- The state Step 1 should hold after `Q` points have been collected:
`S = κ + ∑_{i ≤ Q} G(y_i)`, `C* = C*(Q)`, `r = L(Q) − 1`, `R = R(Q) + 1`. -/
noncomputable def stateAt (κ : ℝ) (G : ℤ → ℝ) (y₁ : ℤ) (Q : ℕ) : OPTState :=
  ⟨κ + ∑ i ∈ Finset.Icc 1 Q, G (y G y₁ i), Q, Cstar κ G y₁ Q, L G y₁ Q - 1, R G y₁ Q + 1⟩

end FedergruenZhengRQ.OPT
