import Mathlib
import Definitions.Def_CostScaling_Refine_Core

namespace CostScaling.Refine

variable {V : Type*} [Fintype V] [DecidableEq V]

def PushApplicable (N : Network V) (s : State V) (v w : V) : Prop :=
  IsActive N s.f v ∧ IsAdmissible N s.f s.p v w

def RelabelApplicable (N : Network V) (s : State V) (v : V) : Prop :=
  IsActive N s.f v ∧
  ∀ w, IsResidualArc N s.f v w → 0 ≤ reducedCost N s.p v w

def pushAmount (N : Network V) (s : State V) (v w : V) : ℝ :=
  min (excess N s.f v) (CycleCanceling.MinMean.resCap N s.f v w)

/-- Figure 5 changes both orientations of the selected edge. -/
def pushFlow (N : Network V) (s : State V) (v w : V) (x y : V) : ℝ :=
  if x = v ∧ y = w then s.f x y + pushAmount N s v w
  else if x = w ∧ y = v then s.f x y - pushAmount N s v w
  else s.f x y

def IsPushStep (N : Network V) (s : State V) (v w : V) (t : State V) : Prop :=
  PushApplicable N s v w ∧ t.f = pushFlow N s v w ∧ t.p = s.p

/-- The minimum in Figure 5 is witnessed by an outgoing residual arc. -/
def IsRelabelStep (N : Network V) (ε : ℝ) (s : State V) (v : V) (t : State V) : Prop :=
  RelabelApplicable N s v ∧
  ∃ w₀, IsResidualArc N s.f v w₀ ∧
    (∀ w, IsResidualArc N s.f v w →
      s.p w₀ + N.c v w₀ + ε ≤ s.p w + N.c v w + ε) ∧
    t.f = s.f ∧
    t.p = Function.update s.p v (s.p w₀ + N.c v w₀ + ε)

def IsStep (N : Network V) (ε : ℝ) (s t : State V) : Prop :=
  (∃ v w, IsPushStep N s v w t) ∨ (∃ v, IsRelabelStep N ε s v t)

/-- A finite prefix of any choice sequence of Figure 4 operations. -/
def IsRun (N : Network V) (ε : ℝ) (f₀ : V → V → ℝ) (p₀ : V → ℝ)
    (σ : ℕ → State V) (K : ℕ) : Prop :=
  σ 0 = initialState N f₀ p₀ ∧ ∀ k < K, IsStep N ε (σ k) (σ (k + 1))

/-- The literal negation of Figure 4's loop guard, using Figure 5 applicability. -/
def Terminated (N : Network V) (s : State V) : Prop :=
  (∀ v w, ¬ PushApplicable N s v w) ∧
  (∀ v, ¬ RelabelApplicable N s v)

def IsSaturatingPush (N : Network V) (s t : State V) : Prop :=
  ∃ v w, IsPushStep N s v w t ∧ CycleCanceling.MinMean.resCap N t.f v w = 0

def IsNonsaturatingPush (N : Network V) (s t : State V) : Prop :=
  ∃ v w, IsPushStep N s v w t ∧ 0 < CycleCanceling.MinMean.resCap N t.f v w

def IsAnyRelabel (N : Network V) (ε : ℝ) (s t : State V) : Prop :=
  ∃ v, IsRelabelStep N ε s v t

noncomputable def relabelCount (N : Network V) (ε : ℝ) (σ : ℕ → State V) (K : ℕ) : ℕ := by
  classical
  exact ((Finset.range K).filter (fun k => IsAnyRelabel N ε (σ k) (σ (k + 1)))).card

noncomputable def saturatingPushCount (N : Network V) (σ : ℕ → State V) (K : ℕ) : ℕ := by
  classical
  exact ((Finset.range K).filter (fun k => IsSaturatingPush N (σ k) (σ (k + 1)))).card

noncomputable def nonsaturatingPushCount (N : Network V) (σ : ℕ → State V) (K : ℕ) : ℕ := by
  classical
  exact ((Finset.range K).filter (fun k => IsNonsaturatingPush N (σ k) (σ (k + 1)))).card

end CostScaling.Refine
