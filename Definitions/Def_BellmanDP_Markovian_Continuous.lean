import Mathlib

namespace BellmanDP.Markovian

open MeasureTheory

/-- Bellman, *Dynamic Programming*, Ch. XI, § 5, (5.1), p. 321: row `i` of
`A(q, t) x + b(q, t)`, namely `Σ_{j=1}^N a_ij(q, t) x_j + b_i(q, t)`, where row `i` depends only
on its own parameter `q : Q i` (§ 3, (3.4), p. 320: the maximization is element by element). -/
def rowAffine {N : ℕ} {Q : Fin N → Type*} (A : (i : Fin N) → Q i → ℝ → Fin N → ℝ)
    (b : (i : Fin N) → Q i → ℝ → ℝ) (i : Fin N) (q : Q i) (t : ℝ) (x : Fin N → ℝ) : ℝ :=
  ∑ j, A i q t j * x j + b i q t

/-- Ch. XI, § 5, Theorem 1, p. 321: `F(t, x) = Max_q [A(q, t) x + b(q, t)]`, taken row by row,
with the maximum over `S i` attained ("the maximum of `A(q, t) x + b(q, t)` is attained for
`q ∈ S` for any fixed `t` and `x` values"). -/
def IsRowwiseMax {N : ℕ} {Q : Fin N → Type*} (A : (i : Fin N) → Q i → ℝ → Fin N → ℝ)
    (b : (i : Fin N) → Q i → ℝ → ℝ) (S : (i : Fin N) → Set (Q i))
    (F : ℝ → (Fin N → ℝ) → Fin N → ℝ) : Prop :=
  ∀ (t : ℝ) (x : Fin N → ℝ) (i : Fin N),
    IsGreatest ((fun q => rowAffine A b i q t x) '' S i) (F t x i)

/-- Ch. XI, § 12, (12.1), p. 332: row `i` of `A(p, q, t) x + b(p, q, t)` in the two-person
version, `Σ_{j=1}^N a_ij(p, q, t) x_j + b_i(p, q, t)`. -/
def rowAffine2 {N : ℕ} {P Q : Fin N → Type*} (A : (i : Fin N) → P i → Q i → ℝ → Fin N → ℝ)
    (b : (i : Fin N) → P i → Q i → ℝ → ℝ) (i : Fin N) (p : P i) (q : Q i) (t : ℝ)
    (x : Fin N → ℝ) : ℝ :=
  ∑ j, A i p q t j * x j + b i p q t

/-- Ch. XI, § 12, Theorem 4, condition (2a), p. 332: `V(t, x)` is, row by row, the common value
`Max_p Min_q [A(p, q, t) x + b(p, q, t)] = Min_q Max_p […]`, both extrema attained: there are
`p̂ ∈ SP i`, `q̂ ∈ SQ i` with `g(p, q̂) ≤ V ≤ g(p̂, q)` for all admissible `p`, `q` (a saddle
point of row `i`'s payoff `g`). -/
def IsRowwiseSaddleValue {N : ℕ} {P Q : Fin N → Type*}
    (A : (i : Fin N) → P i → Q i → ℝ → Fin N → ℝ) (b : (i : Fin N) → P i → Q i → ℝ → ℝ)
    (SP : (i : Fin N) → Set (P i)) (SQ : (i : Fin N) → Set (Q i))
    (V : ℝ → (Fin N → ℝ) → Fin N → ℝ) : Prop :=
  ∀ (t : ℝ) (x : Fin N → ℝ) (i : Fin N), ∃ p₀ ∈ SP i, ∃ q₀ ∈ SQ i,
    (∀ p ∈ SP i, rowAffine2 A b i p q₀ t x ≤ V t x i) ∧
    (∀ q ∈ SQ i, V t x i ≤ rowAffine2 A b i p₀ q t x)

/-- Ch. XI, § 4, (4.2), and § 5, (5.10), pp. 320, 323: `x` is a solution of `dx/dt = F(t, x)`,
`x(0) = c`, on `[0, T]` "satisfying the equation almost everywhere": `x` is continuous on
`[0, T]`, `s ↦ F(s, x(s))` is integrable on `[0, T]`, and
`x(t) = c + ∫_0^t F(s, x(s)) ds` for `0 ≤ t ≤ T`. -/
def IsIntegralSolutionOn {N : ℕ} (F : ℝ → (Fin N → ℝ) → Fin N → ℝ) (c : Fin N → ℝ) (T : ℝ)
    (x : ℝ → Fin N → ℝ) : Prop :=
  ContinuousOn x (Set.Icc 0 T) ∧ IntegrableOn (fun s => F s (x s)) (Set.Icc 0 T) ∧
    ∀ t ∈ Set.Icc 0 T, x t = c + ∫ s in (0 : ℝ)..t, F s (x s)

/-- Ch. XI, § 5, (5.3), p. 321, and § 12, (12.3), p. 332: the successive approximations
`x₀ = c`, `x_{n+1}(t) = c + ∫_0^t F(s, x_n(s)) ds`. -/
noncomputable def picardIter {N : ℕ} (F : ℝ → (Fin N → ℝ) → Fin N → ℝ) (c : Fin N → ℝ) :
    ℕ → ℝ → Fin N → ℝ
  | 0 => fun _ => c
  | n + 1 => fun t => c + ∫ s in (0 : ℝ)..t, F s (picardIter F c n s)

end BellmanDP.Markovian
