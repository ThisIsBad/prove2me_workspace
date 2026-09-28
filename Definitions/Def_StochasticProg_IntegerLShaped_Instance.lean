import Mathlib
import Definitions.Def_StochasticProg_Recourse_Instance

namespace StochasticProg.IntegerLShaped

open StochasticProg.Recourse

variable {n1 n2 m1 m2 K : ℕ}

/-- A stochastic integer program (SIP), Ch. 7 §7.1 Eq. (1.1)-(1.2), p. 289: the same
recourse data as `Recourse.Instance` (first-stage `A, b, c`, fixed recourse `W`, `K`
scenarios of `(q, h, T)` with probabilities `p`), together with a first-stage
restriction `X` ("`x ∈ X`", Eq. (1.1)) and a second-stage integrality (or other)
restriction `Y` on the recourse variable ("`y ∈ Y`", Eq. (1.2)). -/
structure Data (n1 n2 m1 m2 K : ℕ) extends Instance n1 n2 m1 m2 K where
  X : Set (Fin n1 → ℝ)
  Y : Set (Fin n2 → ℝ)

variable (d : Data n1 n2 m1 m2 K)

/-- The second-stage value `Q(x,ξ_k)` with the restriction `y ∈ Y` imposed (Eq. (1.2),
p. 289): `sInf` of the empty set is `⊤` (infeasible), matching the book's convention
(as in `Recourse.QVal`). -/
noncomputable def QValY (d : Data n1 n2 m1 m2 K) (x : Fin n1 → ℝ) (k : Fin K) : EReal :=
  sInf {z : EReal | ∃ y : Fin n2 → ℝ, y ∈ d.Y ∧ (∀ i, 0 ≤ y i) ∧
    Matrix.mulVec d.W y = d.h k - Matrix.mulVec (d.T k) x ∧
    z = ((dotProduct (d.q k) y : ℝ) : EReal)}

/-- `Q(x) = E_ξ Q(x,ξ)` with `Y` imposed (Eq. (1.1)), combined via `Recourse.bookAdd`
(the same `+∞ + (-∞) = +∞` convention, p. 109). -/
noncomputable def QY (d : Data n1 n2 m1 m2 K) (x : Fin n1 → ℝ) : EReal :=
  (List.ofFn (fun k : Fin K => (d.p k : EReal) * QValY d x k)).foldr bookAdd 0

/-- The deterministic-equivalent objective `z(x) = cᵀx + Q(x)` for the SIP, with `Y`
imposed (Eq. (1.1)/(DEP) p. 290). -/
noncomputable def objY (d : Data n1 n2 m1 m2 K) (x : Fin n1 → ℝ) : EReal :=
  ((dotProduct d.c x : ℝ) : EReal) + QY d x

/-- First-stage feasibility for the SIP: `x ∈ K1` (Ch. 3, `Ax = b`, `x ≥ 0`) and
`x ∈ X` (Eq. (1.1)). -/
def K1X (d : Data n1 n2 m1 m2 K) : Set (Fin n1 → ℝ) :=
  K1 d.toInstance ∩ d.X

/-- "It is said to have relatively complete recourse when `K2 ⊇ K1`" (Ch. 3 p. 138),
restated for the `Y`-restricted recourse value of this chapter: every SIP-feasible `x`
is second-stage feasible under `Y`. -/
def RelativelyCompleteRecourse (d : Data n1 n2 m1 m2 K) : Prop :=
  K1X d ⊆ {x | QY d x ≠ ⊤}

/-- "the first-stage variables are binary variables" (§7.2, p. 291). -/
def Binary (x : Fin n1 → ℝ) : Prop := ∀ i, x i = 0 ∨ x i = 1

/-- `δ(x,S) = Σ_{i∈S} x_i − Σ_{i∉S} x_i`, Eq. (2.2), p. 291. -/
def delta (S : Finset (Fin n1)) (x : Fin n1 → ℝ) : ℝ :=
  (∑ i ∈ S, x i) - ∑ i ∈ Sᶜ, x i

/-- The indicator first-stage point "`x_i = 1, i ∈ S`, `x_i = 0, i ∉ S`" of §7.2,
Proposition 3. -/
def indicator (S : Finset (Fin n1)) : Fin n1 → ℝ := fun i => if i ∈ S then 1 else 0

/-- The right-hand side of optimality cut (2.1), p. 291:
`(qS − L)(Σ_{i∈S} x_i − Σ_{i∉S} x_i) − (qS − L)(|S| − 1) + L`. -/
def cutRHS (L qS : ℝ) (S : Finset (Fin n1)) (x : Fin n1 → ℝ) : ℝ :=
  (qS - L) * delta S x - (qS - L) * ((S.card : ℝ) - 1) + L

end StochasticProg.IntegerLShaped
