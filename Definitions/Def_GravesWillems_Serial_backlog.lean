import Mathlib

namespace GravesWillems.Serial

/-- Window demand `d(a, b] = d(a + 1) + ⋯ + d(b)` of a demand path `d : ℤ → ℝ`
(Graves–Willems 2000, §3 p. 72 and Appendix p. 80). It is `0` when `a ≥ b`, as on p. 72. -/
noncomputable def windowDemand (d : ℤ → ℝ) (a b : ℤ) : ℝ :=
  ∑ τ ∈ Finset.Ioc a b, d τ

/-- Auxiliary recursion for the backlog: `backlogAux N T B d r i t` is the backlog at stage `i`
at time `t` computed through `r` further stages; with `r = 0` it is `0` (this is `Q_{N+1} ≡ 0`). -/
noncomputable def backlogAux (T : ℕ → ℕ) (B : ℕ → ℝ) (d : ℤ → ℝ) : ℕ → ℕ → ℤ → ℝ
  | 0, _, _ => 0
  | r + 1, i, t =>
      max 0 (windowDemand d (t - (T i : ℤ)) t + backlogAux T B d r (i + 1) (t - (T i : ℤ)) - B i)

/-- The backlog `Qᵢ(t)` of stage `i` at time `t` in the `N`-stage serial base-stock system with
lead times `T`, base stocks `B` and end-item demand path `d`, defined by the recursion (A1) of
Graves–Willems 2000 (Appendix, p. 81):
`Qᵢ(t) = [d(t − Tᵢ, t] + Q_{i+1}(t − Tᵢ) − Bᵢ]⁺`, with `Q_{N+1}(t) = 0`.
Stages `i ∈ {1, …, N}` are the paper's; `Qᵢ ≡ 0` for `i > N`. The value at `i = 0` is not used. -/
noncomputable def backlog (N : ℕ) (T : ℕ → ℕ) (B : ℕ → ℝ) (d : ℤ → ℝ) (i : ℕ) (t : ℤ) : ℝ :=
  backlogAux T B d (N + 1 - i) i t

end GravesWillems.Serial
