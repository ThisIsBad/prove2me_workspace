import Mathlib
noncomputable section

namespace RiskUncSets.InnerApprox

/-- Definition 4.6: the restricted simplex `Δ̂ᴺ`, probability vectors with
`q₁ ≥ ⋯ ≥ q_N` (indices are 0-based in Lean). -/
def restrictedSimplex (N : ℕ) : Set (Fin N → ℝ) :=
  {q | q ∈ stdSimplex ℝ (Fin N) ∧ Antitone q}

/-- Definition 4.7: the `q`-permutohull `Π_q(𝒜) = conv {∑ᵢ q_{σ(i)} aᵢ : σ ∈ S_N}`.
Defined for every real vector `q`. -/
def permutohull {N n : ℕ} (q : Fin N → ℝ) (a : Fin N → Fin n → ℝ) :
    Set (Fin n → ℝ) :=
  convexHull ℝ (Set.range fun σ : Equiv.Perm (Fin N) => ∑ i, q (σ i) • a i)

/-- The sample mean `â = A e_N = (1/N) ∑ᵢ aᵢ`. -/
def sampleMean {N n : ℕ} (a : Fin N → Fin n → ℝ) : Fin n → ℝ :=
  ∑ i, (1 / (N : ℝ)) • a i

/-- Definition 4.9 with equation (9): the symmetric restricted simplex `Δ̂ᴺ_sym`,
the `q ∈ Δ̂ᴺ` with `q = 2 e_N − q_σ` for some permutation `σ`, `(q_σ)ᵢ = q_{σ(i)}`. -/
def symRestrictedSimplex (N : ℕ) : Set (Fin N → ℝ) :=
  {q | q ∈ restrictedSimplex N ∧
    ∃ σ : Equiv.Perm (Fin N), q = fun i => 2 / (N : ℝ) - q (σ i)}

/-- `π̃_q(𝒜)`: the permutohull `Π_q(𝒜)` shifted by `−â`. -/
def piTilde {N n : ℕ} (q : Fin N → ℝ) (a : Fin N → Fin n → ℝ) : Set (Fin n → ℝ) :=
  (fun w => w - sampleMean a) '' permutohull q a

/-- Equation (12): `‖w‖_{q,𝒜} = inf {α > 0 | w / α ∈ π̃_q(𝒜)}`, the Minkowski functional
(`gauge`) of `π̃_q(𝒜)` evaluated at `w = a − â`. Mathlib's `gauge` is `0`, not `+∞`,
when no positive multiple of the set contains `w`. -/
def normQ {N n : ℕ} (q : Fin N → ℝ) (a : Fin N → Fin n → ℝ) (w : Fin n → ℝ) : ℝ :=
  gauge (piTilde q a) w

/-- The mixture `λ q + (1 − λ) e_N`, with `e_N` the vector with `1/N` at each entry. -/
def mix {N : ℕ} (q : Fin N → ℝ) (lam : ℝ) : Fin N → ℝ :=
  fun i => lam * q i + (1 - lam) * (1 / (N : ℝ))

/-- Equation (14): the polyhedron `𝒰 = {a ∈ ℝⁿ : u_k′ a ≥ v_k, k = 1, …, m}`. -/
def polytope {n m : ℕ} (u : Fin m → Fin n → ℝ) (v : Fin m → ℝ) : Set (Fin n → ℝ) :=
  {a | ∀ k, v k ≤ u k ⬝ᵥ a}

/-- The constraints of the linear program (15) at the value `lam` of `λ`: there are
`q ∈ ℝᴺ` and `s_k, t_k ∈ ℝᴺ` (`k = 1, …, m`) with `q = λ q̂ + (1 − λ) e/N`,
`e′(s_k + t_k) ≥ v_k` and `s_{k,i} + t_{k,j} ≤ (u_k′ a_j) q_i` for all `i, j, k`. -/
def LP15Feasible {N n m : ℕ} (qh : Fin N → ℝ) (a : Fin N → Fin n → ℝ)
    (u : Fin m → Fin n → ℝ) (v : Fin m → ℝ) (lam : ℝ) : Prop :=
  ∃ (q : Fin N → ℝ) (s t : Fin m → Fin N → ℝ), q = mix qh lam ∧
    (∀ k, v k ≤ ∑ i, (s k i + t k i)) ∧
    ∀ k i j, s k i + t k j ≤ (u k ⬝ᵥ a j) * q i

end RiskUncSets.InnerApprox
