import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_F

namespace DoubleGreedyUSM.Fractional

/-- The characteristic vector `1_O ∈ {0,1}^X` of a set `O ⊆ X` (Buchbinder–Feldman–Naor–Schwartz,
FOCS 2012, App. A, PDF p. 9: "we … unify a set with its characteristic vector"). The unit vector
`{u}` of Algorithm 4 is `indicator {u}`. -/
def indicator {X : Type} [DecidableEq X] (O : Finset X) : X → ℝ :=
  fun v => if v ∈ O then 1 else 0

/-- Line 3 of Algorithm 4 (with the slip `a'_i` read as `a_i`): the gain
`a = F(x + {u}) − F(x)` of raising coordinate `u` of `x` by one. -/
noncomputable def aGain {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (x : X → ℝ) (u : X) : ℝ :=
  NonmonotoneSubmod.Shared.F f (x + indicator {u}) - NonmonotoneSubmod.Shared.F f x

/-- Line 4 of Algorithm 4 (with the slip `b'_i` read as `b_i`): the gain
`b = F(y − {u}) − F(y)` of lowering coordinate `u` of `y` by one. -/
noncomputable def bGain {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (y : X → ℝ) (u : X) : ℝ :=
  NonmonotoneSubmod.Shared.F f (y - indicator {u}) - NonmonotoneSubmod.Shared.F f y

/-- One iteration (lines 3–7) of Algorithm 4, MultilinearUSM, on the state `s = (x, y)` and the
element `u`: with `a = aGain f x u`, `b = bGain f y u`, `a' = max a 0`, `b' = max b 0`,
`x ← x + a'/(a' + b') · {u}` and `y ← y − b'/(a' + b') · {u}`, where by the footnote of the
algorithm `a'/(a' + b') = 1` and `b'/(a' + b') = 0` when `a' = b' = 0`. -/
noncomputable def step {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (s : (X → ℝ) × (X → ℝ)) (u : X) : (X → ℝ) × (X → ℝ) :=
  let a' := max (aGain f s.1 u) 0
  let b' := max (bGain f s.2 u) 0
  let t : ℝ := if a' + b' = 0 then 1 else a' / (a' + b')
  let r : ℝ := if a' + b' = 0 then 0 else b' / (a' + b')
  (s.1 + t • indicator {u}, s.2 - r • indicator {u})

/-- The state `(x_i, y_i)` of Algorithm 4 after the first `i` iterations, processing the ground set
in the order `l = [u_1, …, u_n]`, from `x_0 = ∅` (the vector `0`) and `y_0 = 𝒩` (the vector `1`).
For `i ≥ l.length` it is the final state `(x_n, y_n)`. -/
noncomputable def state {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (l : List X) (i : ℕ) : (X → ℝ) × (X → ℝ) :=
  (l.take i).foldl (step f) (0, 1)

/-- `OPT_i = (OPT ∨ x_i) ∧ y_i` (App. A, PDF p. 9): the coordinate-wise minimum of `y_i` and the
coordinate-wise maximum of `1_O` and `x_i`, for the state `s = (x_i, y_i)` and a set `O`. -/
def optI {X : Type} [DecidableEq X] (O : Finset X) (s : (X → ℝ) × (X → ℝ)) : X → ℝ :=
  fun v => min (max (indicator O v) (s.1 v)) (s.2 v)

end DoubleGreedyUSM.Fractional
