import Mathlib

namespace BellmanDP.ExistUnique

/-- Bellman, *Dynamic Programming*, Ch. IV, § 1, Eq. (1.1), p. 116: the one-stage return
`g(p, q) + h(p, q) f(T(p, q))` of choosing `q ∈ S` in state `p` and continuing with `f`. -/
def stageReturn {E S : Type*} (g h : E → S → ℝ) (T : E → S → E) (f : E → ℝ) (p : E) (q : S) :
    ℝ :=
  g p q + h p q * f (T p q)

/-- Eq. (1.1) at the state `p`: `f(p) = Sup_q [g(p, q) + h(p, q) f(T(p, q))]`, the supremum
over `q ∈ S` taken in the genuine sense (`IsLUB`: the set of one-stage returns is bounded above
and `f p` is its least upper bound). -/
def SolvesAt {E S : Type*} (g h : E → S → ℝ) (T : E → S → E) (f : E → ℝ) (p : E) : Prop :=
  IsLUB (Set.range (stageReturn g h T f p)) (f p)

/-- The right-hand side of (1.1) as an operator, `Sup_q [g(p, q) + h(p, q) f(T(p, q))]`, used to
define the successive approximations (3.3b), (4.3). It is a real `iSup`; it is only evaluated
where the returns are bounded above, in which case it is the book's supremum. -/
noncomputable def supOp {E S : Type*} (g h : E → S → ℝ) (T : E → S → E) (f : E → ℝ) (p : E) :
    ℝ :=
  ⨆ q, stageReturn g h T f p q

/-- Ch. IV, Theorem 1, (3a), p. 119, and (4.3), p. 121: the initial approximation
`f₀(p) = Sup_q g(p, q)` (a real `iSup`, evaluated where `g(p, ·)` is bounded). -/
noncomputable def supG {E S : Type*} (g : E → S → ℝ) (p : E) : ℝ :=
  ⨆ q, g p q

/-- Ch. IV, Theorem 1, (3b), p. 119: the successive approximations
`f_{n+1}(p) = Sup_q [g(p, q) + h(p, q) f_n(T(p, q))]` started from `f₀`. -/
noncomputable def succApprox {E S : Type*} (g h : E → S → ℝ) (T : E → S → E) (f₀ : E → ℝ) :
    ℕ → E → ℝ
  | 0 => f₀
  | n + 1 => supOp g h T (succApprox g h T f₀ n)

/-- Ch. IV, § 3, (1e), p. 119, and § 6, Eq. (6.5), p. 124: the radial supremum
`Sup_{‖p‖ ≤ c, p ∈ D} Sup_q |φ(p, q)|`. With `φ = g` this is `v(c)`; with `φ = G − g` it is
`u(c)`. It is a real `sSup`; the theorems use it only where `φ` is bounded on
`{p ∈ D, ‖p‖ ≤ c}` (value `0` if that set is empty). -/
noncomputable def radialSup {E S : Type*} [Norm E] (D : Set E) (φ : E → S → ℝ) (c : ℝ) : ℝ :=
  sSup {x : ℝ | ∃ p ∈ D, ‖p‖ ≤ c ∧ ∃ q : S, x = |φ p q|}

/-- "Bounded in any finite part of `D`" (Ch. IV, Theorem 2, p. 121): `f` is bounded on
`{p ∈ D : ‖p‖ ≤ c}` for every `c`. -/
def BoundedOnBoundedParts {E : Type*} [Norm E] (D : Set E) (f : E → ℝ) : Prop :=
  ∀ c : ℝ, ∃ M : ℝ, ∀ p ∈ D, ‖p‖ ≤ c → |f p| ≤ M

/-- "`φ(p, q)` is continuous in `p` in any bounded portion of `D`, uniformly for all `q ∈ S`"
(Ch. IV, Theorem 1, pp. 119–120), read as uniform equicontinuity: for every `c` and `ε > 0`
there is one `δ > 0` that works for all `q ∈ S` and all `p, p' ∈ D` with `‖p‖, ‖p'‖ ≤ c`. -/
def UnifContInP {E S Y : Type*} [SeminormedAddCommGroup E] [PseudoMetricSpace Y] (D : Set E)
    (φ : E → S → Y) : Prop :=
  ∀ c ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ D, ∀ p' ∈ D, ‖p‖ ≤ c → ‖p'‖ ≤ c →
    dist p p' < δ → ∀ q : S, dist (φ p q) (φ p' q) < ε

end BellmanDP.ExistUnique
