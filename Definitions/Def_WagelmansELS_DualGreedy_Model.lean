import Mathlib

namespace WagelmansELS.DualGreedy

/-- The finite-horizon economic lot-sizing data of Section 1. Periods are `1, …, n`.
The nonnegativity assumptions on demand and setup cost are stated at each theorem. -/
structure Instance where
  n : ℕ
  d : ℕ → ℝ
  f : ℕ → ℝ
  c : ℕ → ℝ

/-- Cumulative demand `d_{i,j}`. -/
def demand (P : Instance) (i j : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc i j, P.d t

/-- The objective of Program D′ through period `j`. -/
def objective (P : Instance) (v : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 j, P.d t * v t

/-- The amount used in constraint `i` of Program D′ through period `j`. -/
def constraintUse (P : Instance) (v : ℕ → ℝ) (i j : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc i j, P.d t * max 0 (v t - P.c i)

/-- Feasibility in Program D′, with every constraint summed through `n`. -/
def IsFeasible (P : Instance) (v : ℕ → ℝ) : Prop :=
  ∀ i, 1 ≤ i → i ≤ P.n → constraintUse P v i P.n ≤ P.f i

/-- Cost of using production period `i` for a terminal block through `j`. -/
def blockCost (P : Instance) (F : ℕ → ℝ) (i j : ℕ) : ℝ :=
  P.f i + P.c i * demand P i j + F (i - 1)

/-- The forward zero-inventory recursion for the cost through period `j`.
At a zero-demand period no production is required. Values beyond the horizon are irrelevant. -/
noncomputable def F (P : Instance) (j : ℕ) : ℝ :=
  (Nat.rec (motive := fun _ => ℕ → ℝ) (fun _ => (0 : ℝ)) (fun k hist =>
    fun t => if t = k + 1 then
      if k + 1 ≤ P.n then
        if P.d (k + 1) = 0 then hist k
        else (Finset.Icc 1 (k + 1)).inf' (by
          refine ⟨1, Finset.mem_Icc.mpr ?_⟩
          omega) (fun i => P.f i + P.c i * demand P i (k + 1) + hist (i - 1))
      else 0
    else hist t) j) j

end WagelmansELS.DualGreedy
