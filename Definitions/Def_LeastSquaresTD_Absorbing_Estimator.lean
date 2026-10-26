import Definitions.Def_LeastSquaresTD_Absorbing_Chain

namespace LeastSquaresTD.Absorbing

open MeasureTheory Filter Topology

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {m : ℕ}

/-- Equation (11) on every transition of an ordinary Markov chain, as in
Lemma 5. -/
noncomputable def chainLstdA (φ : X → Fin m → ℝ) (γ : ℝ)
    (z : ℕ → X) (n : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  ∑ k ∈ Finset.range n,
    Matrix.vecMulVec (φ (z k)) (φ (z k) - γ • φ (z (k + 1)))

/-- The reward sum in (11) on every ordinary-chain transition. -/
noncomputable def chainLstdB (R : X → X → ℝ) (φ : X → Fin m → ℝ)
    (z : ℕ → X) (n : ℕ) : Fin m → ℝ :=
  ∑ k ∈ Finset.range n, R (z k) (z (k + 1)) • φ (z k)

/-- The ordinary-chain LS TD estimate of Lemma 5. The common `1/t` factors
in (11) cancel for positive `t`. -/
noncomputable def chainLstdTheta (R : X → X → ℝ) (φ : X → Fin m → ℝ)
    (γ : ℝ) (z : ℕ → X) (n : ℕ) : Fin m → ℝ :=
  Matrix.mulVec (chainLstdA φ γ z n)⁻¹ (chainLstdB R φ z n)

/-- Equation (11), p. 42, on the transitions performed inside trials in Figure 2.
The paper's factors `1/t` cancel when the matrix is invertible. Restart draws
are excluded, and `n` counts restart-process steps rather than only transitions. -/
noncomputable def lstdA (C : Chain X) (φ : X → Fin m → ℝ) (γ : ℝ)
    (z : ℕ → X) (n : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  ∑ k ∈ (Finset.range n).filter (fun k => C.P (z k) (z k) ≠ 1),
    Matrix.vecMulVec (φ (z k)) (φ (z k) - γ • φ (z (k + 1)))

/-- The reward-weighted feature sum in (11), restricted to in-trial transitions. -/
noncomputable def lstdB (C : Chain X) (R : X → X → ℝ) (φ : X → Fin m → ℝ)
    (z : ℕ → X) (n : ℕ) : Fin m → ℝ :=
  ∑ k ∈ (Finset.range n).filter (fun k => C.P (z k) (z k) ≠ 1),
    R (z k) (z (k + 1)) • φ (z k)

/-- The trial-based LS TD estimate (11). Lean's inverse is total and gives a
default on singular matrices; the convergence result entails eventual nonsingularity. -/
noncomputable def lstdTheta (C : Chain X) (R : X → X → ℝ)
    (φ : X → Fin m → ℝ) (γ : ℝ) (z : ℕ → X) (n : ℕ) : Fin m → ℝ :=
  Matrix.mulVec (lstdA C φ γ z n)⁻¹ (lstdB C R φ z n)

/-- The matrix in Lemma 5, with `Φ` the matrix whose row is `φ x`. -/
noncomputable def limitMatrix (C : Chain X) (φ : X → Fin m → ℝ)
    (γ : ℝ) (π : X → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.transpose (Matrix.of φ) * Matrix.diagonal π * (1 - γ • C.P) * Matrix.of φ

/-- The right-hand vector in Lemma 5. -/
noncomputable def limitVector (C : Chain X) (R : X → X → ℝ)
    (φ : X → Fin m → ℝ) (π : X → ℝ) : Fin m → ℝ :=
  Matrix.mulVec (Matrix.transpose (Matrix.of φ))
    (Matrix.mulVec (Matrix.diagonal π) (C.rbar R))

/-- The cylinder-distribution description of the restart process of Figure 2.
`X` has a discrete measurable space in the theorems. -/
def HasRestartLaw {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (C : Chain X) (S : X → ℝ) (μ : Measure Ω) (Z : ℕ → Ω → X) : Prop :=
  (∀ n, Measurable (Z n)) ∧
  ∀ (n : ℕ) (xs : Fin (n + 1) → X),
    μ {ω | ∀ i : Fin (n + 1), Z i ω = xs i} =
      ENNReal.ofReal (S (xs 0) * ∏ i : Fin n,
        C.restartKernel S (xs i.castSucc) (xs i.succ))

/-- Finite-dimensional distributions of the ordinary Markov chain in
Lemma 5, with arbitrary initial distribution `S`. -/
def HasChainLaw {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (C : Chain X) (S : X → ℝ) (μ : Measure Ω) (Z : ℕ → Ω → X) : Prop :=
  (∀ n, Measurable (Z n)) ∧
  ∀ (n : ℕ) (xs : Fin (n + 1) → X),
    μ {ω | ∀ i : Fin (n + 1), Z i ω = xs i} =
      ENNReal.ofReal (S (xs 0) * ∏ i : Fin n,
        C.P (xs i.castSucc) (xs i.succ))

/-- Empirical proportion of all transitions leaving a state, for Lemma 5. -/
noncomputable def chainOutFrequency (z : ℕ → X) (x : X) (n : ℕ) : ℝ :=
  ((Finset.range n).filter (fun k => z k = x)).card / n

/-- Empirical proportion of in-trial transitions leaving `x`. -/
noncomputable def outFrequency (C : Chain X) (z : ℕ → X) (x : X) (n : ℕ) : ℝ :=
  ((Finset.range n).filter (fun k => C.P (z k) (z k) ≠ 1 ∧ z k = x)).card / n

/-- Empirical proportion of in-trial transitions from `x` to `y`. -/
noncomputable def pairFrequency (C : Chain X) (z : ℕ → X) (x y : X) (n : ℕ) : ℝ :=
  ((Finset.range n).filter (fun k => C.P (z k) (z k) ≠ 1 ∧ z k = x ∧ z (k + 1) = y)).card / n

end LeastSquaresTD.Absorbing
