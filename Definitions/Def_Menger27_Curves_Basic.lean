import Mathlib

namespace Menger27.Curves

/-- Menger's regular point: arbitrarily small open neighbourhoods have finite boundary. -/
def IsRegularPoint {X : Type*} [TopologicalSpace X] (p : X) : Prop :=
  ∀ W : Set X, IsOpen W → p ∈ W →
    ∃ V : Set X, IsOpen V ∧ p ∈ V ∧ V ⊆ W ∧ (frontier V).Finite

/-- Boundary cardinalities at most `n` occur in arbitrarily small neighbourhoods. -/
def OrderAtMost {X : Type*} [TopologicalSpace X] (p : X) (n : ℕ) : Prop :=
  ∀ W : Set X, IsOpen W → p ∈ W →
    ∃ V : Set X, IsOpen V ∧ p ∈ V ∧ V ⊆ W ∧ (frontier V).encard ≤ n

/-- Exact order includes minimality, including the case `n = 0`. -/
def HasOrder {X : Type*} [TopologicalSpace X] (p : X) (n : ℕ) : Prop :=
  OrderAtMost p n ∧ ∀ m : ℕ, m < n → ¬ OrderAtMost p m

/-- A compact connected metric curve all of whose points are regular. -/
def IsRegularCurve (X : Type*) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] : Prop :=
  ∀ p : X, IsRegularPoint p

/-- A parameterized topological arc, with its endpoints at parameters zero and one. -/
def IsArc {X : Type*} [TopologicalSpace X]
    (γ : unitInterval → X) : Prop :=
  Continuous γ ∧ Function.Injective γ

/-- `n` arcs end at `p` and any two meet exactly at `p`. -/
def HasNBein {X : Type*} [TopologicalSpace X] (p : X) (n : ℕ) : Prop :=
  ∃ γ : Fin n → unitInterval → X,
    (∀ i, IsArc (γ i) ∧ γ i 0 = p) ∧
      ∀ i j, i ≠ j → Set.range (γ i) ∩ Set.range (γ j) = {p}

end Menger27.Curves
