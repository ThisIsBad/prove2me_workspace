import Mathlib

namespace NonsmoothNewton.AugLagrangian

/-- The inequality-constraint term of Rockafellar's augmented Lagrangian, Qi–Sun (1993),
p. 363: `φ(r, a, y) = y a + ½ r a²` if `y + r a ≥ 0`, and `-(1/2r) y²` if `y + r a ≤ 0`.
The two branches agree on `y + r a = 0` (both equal `-y²/(2r)`), so the `if` is faithful. -/
noncomputable def phi (r a y : ℝ) : ℝ :=
  if 0 ≤ y + r * a then y * a + r / 2 * a ^ 2 else -(1 / (2 * r)) * y ^ 2

/-- The augmented Lagrangian of the nonlinear program (4.1), Qi–Sun (1993), p. 363:
`L_r(x, y) = f₀(x) + Σ_{i ≤ p} (y_i f_i(x) + ½ r f_i(x)²) + Σ_{i > p} φ(r, f_i(x), y_i)`.
The paper's constraint `i ∈ {1, …, m}` is `i : Fin m` (paper index `i.val + 1`); it is an
equality constraint iff `i.val < p` and an inequality constraint iff `p ≤ i.val`. -/
noncomputable def augLagrangian {n m : ℕ} (p : ℕ) (r : ℝ) (f0 : EuclideanSpace ℝ (Fin n) → ℝ)
    (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) : ℝ :=
  f0 z.1
    + ∑ i ∈ Finset.univ.filter (fun i : Fin m => i.val < p),
        (z.2 i * f i z.1 + r / 2 * f i z.1 ^ 2)
    + ∑ i ∈ Finset.univ.filter (fun i : Fin m => p ≤ i.val), phi r (f i z.1) (z.2 i)

/-- The single inequality term of the proof of Theorem 4.1, Qi–Sun (1993), p. 363:
`η(x, s) = φ(r, g(x), s)` for one constraint function `g = f_i`. -/
noncomputable def eta {n : ℕ} (r : ℝ) (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (z : EuclideanSpace ℝ (Fin n) × ℝ) : ℝ :=
  phi r (g z.1) z.2

end NonsmoothNewton.AugLagrangian
