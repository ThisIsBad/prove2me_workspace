import Mathlib

namespace OnlineRandomization.Tightness

open MeasureTheory

/-- p. 7: a request-answer game with request set `R` and answer set `A`; `cost r a` is
`f_n(r, a)` for `r.length = a.length = n` (requests and answers are lists, oldest first).
Costs are real numbers (the paper allows the value `∞`; a real-valued game is a special case).
The value of `cost` on lists of different lengths is never used. -/
structure Game (R A : Type*) where
  cost : List R → List A → ℝ

/-- p. 7: the off-line optimum `c(r) = min { f_n(r, a) | a ∈ A^n }`, `n = r.length`,
a minimum over the finite nonempty set `A^n`. -/
noncomputable def Game.opt {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A)
    (r : List R) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun a : Fin r.length → A => F.cost r (List.ofFn a))

/-- p. 7: a deterministic online algorithm `(g_i)_{i ≥ 1}`, `g_i : R^i → A`, written as one
function on request lists: `G (r_1, …, r_i) = g_i(r_1, …, r_i)`. Only its values on nonempty
lists are used. -/
abbrev DetAlg (R A : Type*) := List R → A

/-- p. 7: `G(r) = (a_1, …, a_n)` with `a_i = g_i(r_1, …, r_i)`; the `i`-th answer (0-based)
is `G` applied to the first `i + 1` requests. -/
def DetAlg.answers {R A : Type*} (G : DetAlg R A) (r : List R) : List A :=
  (List.range r.length).map fun i => G (r.take (i + 1))

/-- p. 7: the cost `c_G(r) = f_n(r, G(r))` of `G` on the request sequence `r`. -/
def DetAlg.costOn {R A : Type*} (F : Game R A) (G : DetAlg R A) (r : List R) : ℝ :=
  F.cost r (G.answers r)

/-- p. 8: an adaptive off-line adversary `Q = (q_n)_{n = 0, …, d_Q}`,
`q_n : A^n → R ∪ {stop}`: `next a = some x` requests `x` after the answers `a`,
`next a = none` is "stop", and `q_{d_Q}` (hence every `q_n`, `n ≥ d_Q`) only stops. -/
structure OfflineAdv (R A : Type*) where
  next : List A → Option R
  depth : ℕ
  stop_of_le : ∀ a : List A, depth ≤ a.length → next a = none

/-- Auxiliary recursion for `play`: at most `k` further rounds from the position `(r, a)`. -/
def playAux {R A : Type*} (G : DetAlg R A) (Q : OfflineAdv R A) :
    ℕ → List R → List A → List R × List A
  | 0, r, a => (r, a)
  | k + 1, r, a =>
    match Q.next a with
    | none => (r, a)
    | some x => playAux G Q k (r ++ [x]) (a ++ [G (r ++ [x])])

/-- p. 8: the play `(r(G, Q), a(G, Q))`, built in the order `r_1, a_1, r_2, a_2, …` with
`r_{i+1} = q_i(a_1, …, a_i)` and `a_i = g_i(r_1, …, r_i)`, until `Q` stops. -/
def play {R A : Type*} (G : DetAlg R A) (Q : OfflineAdv R A) : List R × List A :=
  playAux G Q Q.depth [] []

/-- p. 8: the cost `c_G(Q) = f_n(r(G, Q), a(G, Q))` of the algorithm against `Q`. -/
def algCostOffline {R A : Type*} (F : Game R A) (G : DetAlg R A) (Q : OfflineAdv R A) : ℝ :=
  F.cost (play G Q).1 (play G Q).2

/-- p. 8: the cost `c_Q(G) = c(r(G, Q))` of the adaptive off-line adversary. -/
noncomputable def advCostOffline {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A)
    (G : DetAlg R A) (Q : OfflineAdv R A) : ℝ :=
  F.opt (play G Q).1

/-- p. 8: an adaptive on-line adversary `S = (Q, P)`: an adaptive off-line adversary together
with answer rules `p_n : A^n → A`. -/
structure OnlineAdv (R A : Type*) extends OfflineAdv R A where
  ans : List A → A

/-- p. 8: the adversary's own answers `b(G, S) = (b_1, …, b_n)`, `b_{i+1} = p_i(a_1, …, a_i)`,
`n = n(G, Q)`. -/
def onlineAnswers {R A : Type*} (G : DetAlg R A) (S : OnlineAdv R A) : List A :=
  let a := (play G S.toOfflineAdv).2
  (List.range a.length).map fun i => S.ans (a.take i)

/-- p. 8: the cost `c_S(G) = f_n(r(G, S), b(G, S))` of the adaptive on-line adversary. -/
def advCostOnline {R A : Type*} (F : Game R A) (G : DetAlg R A) (S : OnlineAdv R A) : ℝ :=
  F.cost (play G S.toOfflineAdv).1 (onlineAnswers G S)

/-- p. 7: a randomized online algorithm, a probability distribution over deterministic online
algorithms `G_x`: a probability space of coin tosses `x ∈ Ω` and a deterministic algorithm
`alg x` for each `x`, such that each answer `g_i(r)` is a measurable function of the coins. -/
structure RandAlg (R A Ω : Type*) [MeasurableSpace Ω] where
  μ : Measure Ω
  isProb : IsProbabilityMeasure μ
  alg : Ω → DetAlg R A
  meas : ∀ (r : List R) (x : A), MeasurableSet {ω | alg ω r = x}

/-- p. 7: a deterministic algorithm `G` is `α`-competitive: `c_G(r) ≤ α(c(r))` for every
request sequence `r`. -/
def IsCompetitive {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A) (α : ℝ → ℝ)
    (G : DetAlg R A) : Prop :=
  ∀ r : List R, G.costOn F r ≤ α (F.opt r)

/-- p. 7: a randomized algorithm is `α`-competitive (against any oblivious adversary):
`E_x[c_{G_x}(r)] ≤ α(c(r))` for every request sequence `r`. -/
def IsCompetitiveObl {R A Ω : Type*} [Fintype A] [Nonempty A] [MeasurableSpace Ω]
    (F : Game R A) (α : ℝ → ℝ) (G : RandAlg R A Ω) : Prop :=
  ∀ r : List R, ∫ ω, (G.alg ω).costOn F r ∂G.μ ≤ α (F.opt r)

/-- p. 9: `α`-competitive against any adaptive off-line adversary:
`E_x[c_{G_x}(Q)] ≤ E_x[α(c_Q(G_x))]` for every adaptive off-line adversary `Q`. -/
def IsCompetitiveOffline {R A Ω : Type*} [Fintype A] [Nonempty A] [MeasurableSpace Ω]
    (F : Game R A) (α : ℝ → ℝ) (G : RandAlg R A Ω) : Prop :=
  ∀ Q : OfflineAdv R A,
    ∫ ω, algCostOffline F (G.alg ω) Q ∂G.μ ≤ ∫ ω, α (advCostOffline F (G.alg ω) Q) ∂G.μ

/-- p. 9: `α`-competitive against any adaptive on-line adversary:
`E_x[c_{G_x}(S)] ≤ E_x[α(c_S(G_x))]` for every adaptive on-line adversary `S`
(note `c_{G_x}(S) = c_{G_x}(Q)` for `S = (Q, P)`, p. 8). -/
def IsCompetitiveOnline {R A Ω : Type*} [Fintype A] [Nonempty A] [MeasurableSpace Ω]
    (F : Game R A) (α : ℝ → ℝ) (G : RandAlg R A Ω) : Prop :=
  ∀ S : OnlineAdv R A,
    ∫ ω, algCostOffline F (G.alg ω) S.toOfflineAdv ∂G.μ ≤
      ∫ ω, α (advCostOnline F (G.alg ω) S) ∂G.μ

end OnlineRandomization.Tightness
