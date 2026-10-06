import Mathlib

namespace OnlineRandomization.Potential

open MeasureTheory

/-- Manuscript p. 7: a request-answer game with request set `R` and answer set `A`.
For lists of equal length `n`, `cost r a` is the paper's `f_n(r, a)`; its value on lists of
different lengths is never used. Costs are real (the paper allows the value `∞`). -/
structure Game (R A : Type*) where
  cost : List R → List A → ℝ

/-- Manuscript p. 7: the off-line optimum `c(r) = min { f_n(r, a) | a ∈ A^n }`, a minimum over
the finite nonempty set `A^n`. -/
noncomputable def Game.opt {R A : Type*} [Fintype A] [Nonempty A]
    (F : Game R A) (r : List R) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty
    (fun a : Fin r.length → A => F.cost r (List.ofFn a))

/-- Manuscript p. 7: the paper's "linear" functions `α, β : ℝ → ℝ` are affine,
`α(x) = c·x + d`. -/
def IsLinear (α : ℝ → ℝ) : Prop :=
  ∃ c d : ℝ, ∀ x : ℝ, α x = c * x + d

/-- Manuscript p. 7: a deterministic online algorithm `(g_i)_{i ≥ 1}`, `g_i : R^i → A`,
represented as one function on request lists; `G (r_1, …, r_i)` is `g_i(r_1, …, r_i)`.
Its value on the empty list is never used. -/
abbrev DetAlg (R A : Type*) := List R → A

/-- Manuscript p. 7: `G(r) = (a_1, …, a_n)` with `a_i = g_i(r_1, …, r_i)`; list index `i`
(0-based) holds the paper's `a_{i+1}`. -/
def DetAlg.answers {R A : Type*} (G : DetAlg R A) (r : List R) : List A :=
  (List.range r.length).map fun i => G (r.take (i + 1))

/-- Manuscript p. 7: the cost `c_G(r) = f_n(r, G(r))`. -/
def DetAlg.costOn {R A : Type*} (F : Game R A) (G : DetAlg R A) (r : List R) : ℝ :=
  F.cost r (G.answers r)

/-- Manuscript p. 8: an adaptive off-line adversary `Q = (q_n)`, `q_n : A^n → R ∪ {stop}`,
with `none` for "stop" and a depth bound `d_Q` from which on it always stops. -/
structure OfflineAdv (R A : Type*) where
  next : List A → Option R
  depth : ℕ
  stop_of_le : ∀ a : List A, depth ≤ a.length → next a = none

/-- Manuscript p. 8: an adaptive on-line adversary `S = (Q, P)`; `ans (a_1, …, a_i)` is
`p_i(a_1, …, a_i)`, the adversary's own answer `b_{i+1}` to its request `r_{i+1}`. -/
structure OnlineAdv (R A : Type*) extends OfflineAdv R A where
  ans : List A → A

/-- Manuscript p. 7: a randomized online algorithm in mixed form, a probability distribution
over deterministic online algorithms `G_x`, `x` the coins. Each answer is a measurable function
of the coins. -/
structure RandAlg (R A Ω : Type*) [MeasurableSpace Ω] where
  μ : Measure Ω
  isProb : IsProbabilityMeasure μ
  alg : Ω → DetAlg R A
  meas : ∀ (r : List R) (x : A), MeasurableSet {ω | alg ω r = x}

/-- Manuscript p. 7: a deterministic algorithm `G` is `α`-competitive if
`c_G(r) ≤ α(c(r))` for every request sequence `r`. For a deterministic algorithm this is also
competitiveness against adaptive adversaries (p. 8). -/
def IsCompetitive {R A : Type*} [Fintype A] [Nonempty A]
    (F : Game R A) (α : ℝ → ℝ) (G : DetAlg R A) : Prop :=
  ∀ r : List R, G.costOn F r ≤ α (F.opt r)

/-- Manuscript p. 7: a randomized algorithm `H` is `β`-competitive against any oblivious
adversary if `E_y[c_{H_y}(r)] ≤ β(c(r))` for every request sequence `r`. -/
def IsCompetitiveObl {R A Ω : Type*} [Fintype A] [Nonempty A] [MeasurableSpace Ω]
    (F : Game R A) (β : ℝ → ℝ) (H : RandAlg R A Ω) : Prop :=
  ∀ r : List R, (∫ y, (H.alg y).costOn F r ∂H.μ) ≤ β (F.opt r)

end OnlineRandomization.Potential
