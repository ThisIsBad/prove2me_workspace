import Mathlib
import Definitions.Def_FatkhullinPolyak_Discrete_Matrix

namespace FatkhullinPolyak.Discrete

/-- The set `S` of stabilizing static output-feedback gains `K ∈ ℝ^{m×r}`: those for which the
closed-loop matrix `A_K = A − BKC` is Hurwitz (p. 3). -/
def stabSet {n m r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) : Set (Matrix (Fin m) (Fin r) ℝ) :=
  {K | IsHurwitz (A - B * K * C)}

/-- `X(K)`: the solution of the Lyapunov equation (2.7),
`(A − BKC)ᵀ X + X (A − BKC) + CᵀKᵀRKC + Q = 0` (p. 4). Unique for `K ∈ S`. -/
noncomputable def lyapX {n m r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (K : Matrix (Fin m) (Fin r) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  lyapSol (A - B * K * C) (C.transpose * K.transpose * R * K * C + Q)

/-- `Y(K)`: the solution of the Lyapunov equation (3.4), `A_K Y + Y A_Kᵀ + Σ = 0` with
`A_K = A − BKC` (p. 7). Unique for `K ∈ S`. -/
noncomputable def lyapY {n m r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ)
    (K : Matrix (Fin m) (Fin r) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  lyapSol (A - B * K * C).transpose Sig

/-- The LQR cost `f(K) = Tr(X(K) Σ)` of Problem 2.2, (2.6) (p. 4). Meaningful for `K ∈ S`. -/
noncomputable def lqrCost {n m r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (Sig : Matrix (Fin n) (Fin n) ℝ) (K : Matrix (Fin m) (Fin r) ℝ) : ℝ :=
  Matrix.trace (lyapX A B C Q R K * Sig)

/-- The gradient formula (3.3): `∇f(K) = 2 (RKC − Bᵀ X(K)) Y(K) Cᵀ` (p. 7). Lemma 3.11 is the
theorem that this is the gradient of `f` on `S`. -/
noncomputable def lqrGrad {n m r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (Sig : Matrix (Fin n) (Fin n) ℝ) (K : Matrix (Fin m) (Fin r) ℝ) : Matrix (Fin m) (Fin r) ℝ :=
  (2 : ℝ) • ((R * K * C - B.transpose * lyapX A B C Q R K) * lyapY A B C Sig K * C.transpose)

/-- The sublevel set `S₀ = {K ∈ S : f(K) ≤ f(K₀)}` (p. 3). -/
def sublevel {n m r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (Sig : Matrix (Fin n) (Fin n) ℝ) (K₀ : Matrix (Fin m) (Fin r) ℝ) :
    Set (Matrix (Fin m) (Fin r) ℝ) :=
  {K | K ∈ stabSet A B C ∧ lqrCost A B C Q R Sig K ≤ lqrCost A B C Q R Sig K₀}

/-- The iterates of the gradient method (4.4), `K_{j+1} = K_j − γ_j ∇f(K_j)`, started at the
known stabilizing gain `K₀` (p. 10), with step sequence `γ`. -/
noncomputable def gradIter {n m r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (Sig : Matrix (Fin n) (Fin n) ℝ) (K₀ : Matrix (Fin m) (Fin r) ℝ) (γ : ℕ → ℝ) :
    ℕ → Matrix (Fin m) (Fin r) ℝ
  | 0 => K₀
  | j + 1 => gradIter A B C Q R Sig K₀ γ j - γ j • lqrGrad A B C Q R Sig (gradIter A B C Q R Sig K₀ γ j)

end FatkhullinPolyak.Discrete
