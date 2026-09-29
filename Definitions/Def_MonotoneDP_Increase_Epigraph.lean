import Mathlib
import Definitions.Def_MonotoneDP_Increase_Model

namespace MonotoneDP.Increase

open Filter Topology

/-- The epigraph of `J ∈ F`, eq. (53): `E(J) = {(x, λ) | J(x) ≤ λ} ⊆ S × (−∞, ∞)`. -/
def E {S : Type*} (J : S → EReal) : Set (S × ℝ) := {p | J p.1 ≤ (p.2 : EReal)}

/-- The closure in `λ` at fixed `x` of eqs. (57) and (63):
`\overline{B} = {(x, λ) | ∃ {λ_n} s.t. λ_n → λ, (x, λ_n) ∈ B, n = 0, 1, …}`, with real `λ_n`
converging in `ℝ`. This is not the topological closure in `S × ℝ`. -/
def Pbar {S : Type*} (B : Set (S × ℝ)) : Set (S × ℝ) :=
  {p | ∃ lam : ℕ → ℝ, Tendsto lam atTop (𝓝 p.2) ∧ ∀ n, (p.1, lam n) ∈ B}

namespace Model

variable {S C : Type*} (m : Model S C)

/-- The set `C_k ⊆ S × C × (−∞, ∞)` of eq. (55), for `k ≥ 1`:
`C_k = {(x, u, λ) | H[x, u, T^{k−1}(J̄)] ≤ λ, x ∈ S, u ∈ U(x)}`.
Only indices `k ≥ 1` are used (at `k = 0` the natural-number subtraction makes `Ck 0 = Ck 1`,
which never occurs in a statement). -/
def Ck (k : ℕ) : Set (S × C × ℝ) :=
  {p | p.2.1 ∈ m.U p.1 ∧ m.H p.1 p.2.1 ((m.T)^[k - 1] m.Jbar) ≤ (p.2.2 : EReal)}

/-- The projection of `A ⊆ S × C × (−∞, ∞)` on `S × (−∞, ∞)` through admissible controls,
eqs. (56) and (62): `P(A) = {(x, λ) | ∃ u ∈ U(x) s.t. (x, u, λ) ∈ A}`. -/
def P (A : Set (S × C × ℝ)) : Set (S × ℝ) := {p | ∃ u ∈ m.U p.1, (p.1, u, p.2) ∈ A}

end Model

end MonotoneDP.Increase
