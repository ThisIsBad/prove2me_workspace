import Mathlib

namespace NonmonotoneSubmod.LocalSearch

/-- The acceptance factor `1 + ε / n²` of Algorithm LS (Feige–Mirrokni–Vondrák 2011, p. 1141),
where `n = |X|` is the number of elements of the ground set. -/
noncomputable def lsFactor (X : Type) [Fintype X] (ε : ℝ) : ℝ :=
  1 + ε / (Fintype.card X : ℝ) ^ 2

/-- One step of Algorithm LS (Feige–Mirrokni–Vondrák 2011, p. 1141, steps 2–3), as a relation
allowing every choice of element the text allows. With `c = 1 + ε / n²`:
* (step 2) if some `a ∉ S` has `f (S ∪ {a}) > c · f S`, the step may move to `S ∪ {a}`;
* (step 3) only when no such addition exists, if some `a ∈ S` has `f (S \ {a}) > c · f S`, the
  step may move to `S \ {a}`. -/
def lsStep {X : Type} [Fintype X] [DecidableEq X] (ε : ℝ) (f : Finset X → ℝ)
    (S S' : Finset X) : Prop :=
  (∃ a, a ∉ S ∧ lsFactor X ε * f S < f (insert a S) ∧ S' = insert a S) ∨
    ((∀ a, a ∉ S → f (insert a S) ≤ lsFactor X ε * f S) ∧
      ∃ a, a ∈ S ∧ lsFactor X ε * f S < f (S.erase a) ∧ S' = S.erase a)

/-- `v` is a singleton of maximum value: `f {w} ≤ f {v}` for every `w ∈ X` (Algorithm LS,
step 1). Ties are not broken: every maximizing `v` is allowed. -/
def IsMaxSingleton {X : Type} (f : Finset X → ℝ) (v : X) : Prop :=
  ∀ w : X, f {w} ≤ f {v}

/-- `S 0, S 1, …, S k` is a run of `k` steps of Algorithm LS: it starts (step 1) at `{v}` for a
singleton `v` of maximum value, and each `S (i + 1)` arises from `S i` by an LS step. -/
def IsLSRun {X : Type} [Fintype X] [DecidableEq X] (ε : ℝ) (f : Finset X → ℝ)
    (S : ℕ → Finset X) (k : ℕ) : Prop :=
  (∃ v : X, IsMaxSingleton f v ∧ S 0 = {v}) ∧ ∀ i, i < k → lsStep ε f (S i) (S (i + 1))

/-- Algorithm LS has terminated at `S`: no step (addition of step 2 or removal of step 3)
applies. -/
def IsLSTerminal {X : Type} [Fintype X] [DecidableEq X] (ε : ℝ) (f : Finset X → ℝ)
    (S : Finset X) : Prop :=
  ∀ S' : Finset X, ¬ lsStep ε f S S'

/-- The value returned by Algorithm LS at the final set `S` (step 4): the maximum of `f(S)` and
`f(X \ S)`. -/
def lsOutput {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ) (S : Finset X) : ℝ :=
  max (f S) (f Sᶜ)

end NonmonotoneSubmod.LocalSearch
