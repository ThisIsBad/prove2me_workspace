import Definitions.Def_OnlineRandomization_Simulation_Game

namespace OnlineRandomization.Simulation

open MeasureTheory

/-- `g_i : R^i → A`, represented by a function on prefixes. Its empty-list
value is unused. -/
abbrev DetAlg (R A : Type*) := List R → A

/-- The successive answers, oldest first; list index `i` is paper index `i+1`. -/
def DetAlg.answers {R A : Type*} (G : DetAlg R A) (r : List R) : List A :=
  (List.range r.length).map fun i => G (r.take (i + 1))

/-- The cost of a deterministic algorithm on a fixed request string. -/
def DetAlg.costOn {R A : Type*} (F : Game R A) (G : DetAlg R A)
    (r : List R) : ℝ := F.cost r (G.answers r)

/-- An adaptive off-line adversary with a uniform finite depth bound. -/
structure OfflineAdv (R A : Type*) where
  next : List A → Option R
  depth : ℕ
  stop_of_le : ∀ a : List A, depth ≤ a.length → next a = none

/-- Alternating requests and algorithm answers, stopping at `none` or depth. -/
def playAux {R A : Type*} (G : DetAlg R A) (Q : OfflineAdv R A) :
    ℕ → List R → List A → List R × List A
  | 0, r, a => (r, a)
  | k + 1, r, a =>
    match Q.next a with
    | none => (r, a)
    | some x => playAux G Q k (r ++ [x]) (a ++ [G (r ++ [x])])

/-- The complete play from the empty position. -/
def play {R A : Type*} (G : DetAlg R A) (Q : OfflineAdv R A) :
    List R × List A := playAux G Q Q.depth [] []

/-- An adaptive on-line adversary also answers each request immediately. -/
structure OnlineAdv (R A : Type*) extends OfflineAdv R A where
  ans : List A → A

/-- The on-line adversary's own answer string, oldest first. -/
def onlineAnswers {R A : Type*} (G : DetAlg R A) (S : OnlineAdv R A) : List A :=
  let a := (play G S.toOfflineAdv).2
  (List.range a.length).map fun i => S.ans (a.take i)

/-- A randomized algorithm is a probability distribution on deterministic
prefix algorithms. Each answer is measurable as a function of the coins. -/
structure RandAlg (R A Ω : Type*) [MeasurableSpace Ω] where
  μ : Measure Ω
  isProb : IsProbabilityMeasure μ
  alg : Ω → DetAlg R A
  meas : ∀ (r : List R) (x : A), MeasurableSet {ω | alg ω r = x}

/-- Deterministic competitiveness against fixed request strings. -/
def IsCompetitive {R A : Type*} [Fintype A] [Nonempty A]
    (F : Game R A) (α : ℝ → ℝ) (G : DetAlg R A) : Prop :=
  ∀ r : List R, G.costOn F r ≤ α (F.opt r)

/-- Expected competitiveness against oblivious adversaries. -/
def IsCompetitiveObl {R A Ω : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace Ω] (F : Game R A) (β : ℝ → ℝ)
    (H : RandAlg R A Ω) : Prop :=
  ∀ r : List R, (∫ ω, (H.alg ω).costOn F r ∂H.μ) ≤ β (F.opt r)

/-- Expected competitiveness against adaptive off-line adversaries. The
cost transform stays inside the expectation, as on manuscript p. 9. -/
def IsCompetitiveOffline {R A Ω : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace Ω] (F : Game R A) (α : ℝ → ℝ)
    (H : RandAlg R A Ω) : Prop :=
  ∀ Q : OfflineAdv R A,
    (∫ ω, F.cost (play (H.alg ω) Q).1 (play (H.alg ω) Q).2 ∂H.μ) ≤
      (∫ ω, α (F.opt (play (H.alg ω) Q).1) ∂H.μ)

/-- Expected competitiveness against adaptive on-line adversaries. -/
def IsCompetitiveOnline {R A Ω : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace Ω] (F : Game R A) (α : ℝ → ℝ)
    (H : RandAlg R A Ω) : Prop :=
  ∀ S : OnlineAdv R A,
    (∫ ω, F.cost (play (H.alg ω) S.toOfflineAdv).1
      (play (H.alg ω) S.toOfflineAdv).2 ∂H.μ) ≤
      (∫ ω, α (F.cost (play (H.alg ω) S.toOfflineAdv).1
        (onlineAnswers (H.alg ω) S)) ∂H.μ)

end OnlineRandomization.Simulation
