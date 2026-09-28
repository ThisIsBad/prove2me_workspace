import Mathlib

namespace StochasticProg.Recourse

/-- A two-stage stochastic linear program with fixed recourse and a finite scenario
set (Birge & Louveaux, Ch. 3, Section 3.1a-b, Eq. (1.1)-(1.4)): first-stage data
`A, b, c` and fixed recourse matrix `W`, together with `K` equally-indexed
realisations of the random data `(q, h, T)` and their probabilities `p`. -/
structure Instance (n1 n2 m1 m2 K : ℕ) where
  A : Matrix (Fin m1) (Fin n1) ℝ
  b : Fin m1 → ℝ
  c : Fin n1 → ℝ
  W : Matrix (Fin m2) (Fin n2) ℝ
  q : Fin K → Fin n2 → ℝ
  h : Fin K → Fin m2 → ℝ
  T : Fin K → Matrix (Fin m2) (Fin n1) ℝ
  p : Fin K → ℝ
  hp_nonneg : ∀ k, 0 ≤ p k
  hp_sum : ∑ k, p k = 1

variable {n1 n2 m1 m2 K : ℕ}

/-- `K1 = {x | Ax = b, x ≥ 0}` (p. 105), the first-stage feasible region. -/
def K1 (inst : Instance n1 n2 m1 m2 K) : Set (Fin n1 → ℝ) :=
  {x | Matrix.mulVec inst.A x = inst.b ∧ ∀ i, 0 ≤ x i}

/-- The second-stage value `Q(x,ξ_k) = min_y {q(ω)ᵀy | Wy = h(ω) - T(ω)x, y ≥ 0}`
(Eq. (1.6), p. 106), as an extended real: `sInf` of the empty set is `⊤` (infeasible)
and `sInf` of a set unbounded below is `⊥` (unbounded), matching the book's stated
conventions for these two failure modes (p. 109). -/
noncomputable def QVal (inst : Instance n1 n2 m1 m2 K) (x : Fin n1 → ℝ) (k : Fin K) : EReal :=
  sInf {z : EReal | ∃ y : Fin n2 → ℝ, (∀ i, 0 ≤ y i) ∧
    Matrix.mulVec inst.W y = inst.h k - Matrix.mulVec (inst.T k) x ∧
    z = ((dotProduct (inst.q k) y : ℝ) : EReal)}

/-- Addition of extended second-stage values under the book's explicit convention
`+∞ + (-∞) = +∞` (p. 109): infeasibility of any scenario dominates unboundedness of
another. This is the opposite convention from Mathlib's `EReal` addition
(`⊥ + ⊤ = ⊤ + ⊥ = ⊥`), so the aggregate recourse value below is built from this
operation rather than from `EReal`'s own `+`. -/
noncomputable def bookAdd (a b : EReal) : EReal := if a = ⊤ ∨ b = ⊤ then ⊤ else a + b

/-- The expected second-stage value `Q(x) = E_ξ Q(x,ξ) = Σ_k p_k Q(x,ξ_k)` for a
finite scenario set (Eq. (1.3) together with p. 106), combined via `bookAdd`. -/
noncomputable def Q (inst : Instance n1 n2 m1 m2 K) (x : Fin n1 → ℝ) : EReal :=
  (List.ofFn (fun k : Fin K => (inst.p k : EReal) * QVal inst x k)).foldr bookAdd 0

/-- `K2 = {x | Q(x) < ∞}` (p. 109), the second-stage feasibility set. -/
def K2 (inst : Instance n1 n2 m1 m2 K) : Set (Fin n1 → ℝ) :=
  {x | Q inst x ≠ ⊤}

/-- The deterministic-equivalent objective `z(x) = cᵀx + Q(x)` (Eq. (1.2), p. 104). -/
noncomputable def obj (inst : Instance n1 n2 m1 m2 K) (x : Fin n1 → ℝ) : EReal :=
  ((dotProduct inst.c x : ℝ) : EReal) + Q inst x

end StochasticProg.Recourse
