import Mathlib

namespace MassartDKW.Tight

/-- Smirnov's point probabilities `p_{λ,n}(j)` of (2.1):
`λ√n (j + λ√n)^{j−1} (n − j − λ√n)^{n−j} n^{−n} C(n, j)`.
The exponent `j − 1` is an integer (`zpow`), so that `p_{λ,n}(0) = (1 − λ/√n)^n`. -/
noncomputable def smirnovP (l : ℝ) (n j : ℕ) : ℝ :=
  l * Real.sqrt n * ((j : ℝ) + l * Real.sqrt n) ^ ((j : ℤ) - 1) *
    ((n : ℝ) - j - l * Real.sqrt n) ^ (n - j) * ((n : ℝ) ^ n)⁻¹ * (n.choose j)

/-- The right side of (2.3): `Σ_{0 ≤ j < n − λ√n} p_{λ,n}(j)`. -/
noncomputable def smirnovTail (n : ℕ) (l : ℝ) : ℝ :=
  ∑ j ∈ (Finset.range n).filter (fun j : ℕ => (j : ℝ) < n - l * Real.sqrt n), smirnovP l n j

/-- Csáki's density (2.2) of the first passage time of a Brownian bridge at level `λ`:
`f_λ(s) = λ/√(2π) s^{−3/2} (1 − s)^{−1/2} exp(−λ²/(2s(1 − s)))`, meaningful for `s ∈ ]0, 1[`. -/
noncomputable def csakiDensity (l s : ℝ) : ℝ :=
  l / Real.sqrt (2 * Real.pi) * s ^ (-(3 / 2 : ℝ)) * (1 - s) ^ (-(1 / 2 : ℝ)) *
    Real.exp (-(l ^ 2) / (2 * s * (1 - s)))

/-- `v_n(s) = (s (s² − 1/(4n²)))^{−1}` (statement of Proposition 1). -/
noncomputable def v (n : ℕ) (s : ℝ) : ℝ :=
  (s * (s ^ 2 - 1 / (4 * (n : ℝ) ^ 2)))⁻¹

/-- `C_{λ,n} = exp(2λ²) Σ_{0 ≤ j < n − λ√n} p_{λ,n}(j)`, i.e. `exp(2λ²) P(D_n⁻ > λ)` through (2.3). -/
noncomputable def C (n : ℕ) (l : ℝ) : ℝ :=
  Real.exp (2 * l ^ 2) * smirnovTail n l

/-- `φ(t) = t − t²/(2(1 + 2t/3)) − log(1 + t)` (Lemma 1). -/
noncomputable def phi (t : ℝ) : ℝ :=
  t - t ^ 2 / (2 * (1 + 2 * t / 3)) - Real.log (1 + t)

/-- `ψ(t) = −log(1 + t) + (3/2) log(1 + 2t/3)` (2.6). -/
noncomputable def psi (t : ℝ) : ℝ :=
  -Real.log (1 + t) + 3 / 2 * Real.log (1 + 2 * t / 3)

/-- `T(ν, t) = ν² φ(t) − ν t ψ(t) + θ t²/(1 + 2t/3)` with `θ = 0.4833` (Lemma 2). -/
noncomputable def T (ν t : ℝ) : ℝ :=
  ν ^ 2 * phi t - ν * t * psi t + 0.4833 * t ^ 2 / (1 + 2 * t / 3)

/-- `I_{a,b}(λ) = λ exp(2λ²)/√(2π) ∫_0^1 u^{−1/2−a} (1 − u)^{−1/2−b} exp(−λ²/(2u(1 − u))) du`
(Lemma 4). -/
noncomputable def I (a b l : ℝ) : ℝ :=
  l * Real.exp (2 * l ^ 2) / Real.sqrt (2 * Real.pi) *
    ∫ u in (0 : ℝ)..1, u ^ (-(1 / 2 : ℝ) - a) * (1 - u) ^ (-(1 / 2 : ℝ) - b) *
      Real.exp (-(l ^ 2) / (2 * u * (1 - u)))

/-- The constant `μ = 0.4345` of the proof of Theorem 1 (p. 1279). -/
noncomputable def mu : ℝ := 0.4345

/-- `η_n(λ)`, the right side of (2.11):
`−1 + (λ + 1/(4λ) + 3μ/λ + 3μ/(2λ³)) n^{−1/2} − (μ/2)(4 + 1/λ²) n^{−1} + (μ/2)(4λ + 1/λ) n^{−3/2}`. -/
noncomputable def eta (n : ℕ) (l : ℝ) : ℝ :=
  -1 + (l + 1 / (4 * l) + 3 * mu / l + 3 * mu / (2 * l ^ 3)) * (n : ℝ) ^ (-(1 / 2 : ℝ))
    - mu / 2 * (4 + 1 / l ^ 2) * (n : ℝ) ^ (-(1 : ℝ))
    + mu / 2 * (4 * l + 1 / l) * (n : ℝ) ^ (-(3 / 2 : ℝ))

end MassartDKW.Tight
