import Mathlib

namespace ChinesePostman.Polyhedron

open Classical

/-! The graph has finite node and edge types, with parallel edges allowed and loops excluded
(§2, p. 89; §3, p. 91). -/

/-- A graph with a separate identity for every edge, including parallel edges. -/
structure Graph (V E : Type) where
  ends : E → Sym2 V
  loopless : ∀ e, ¬ (ends e).IsDiag

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- p. 90: the degree of node `n`, the number of edges meeting `n` (`Σ_e a_ne`). -/
noncomputable def degree (G : Graph V E) (n : V) : ℕ :=
  (Finset.univ.filter (fun e => n ∈ G.ends e)).card

/-- p. 90: `b_n`, equal to `1` when node `n` has odd degree (an *odd node*) and `0` otherwise. -/
noncomputable def bParity (G : Graph V E) (n : V) : ℤ :=
  if Odd (degree G n) then 1 else 0

/-- p. 91: edge `e` *meets* the node set `S` when it meets exactly one node in `S` and one node
not in `S`. -/
def Meets (G : Graph V E) (e : E) (S : Finset V) : Prop :=
  ∃ u v, G.ends e = s(u, v) ∧ u ∈ S ∧ v ∉ S

/-- p. 91: `S` is an *odd set* when it contains an odd number of odd nodes (and any number of
even nodes). -/
def IsOddSet (G : Graph V E) (S : Finset V) : Prop :=
  Odd (S.filter (fun n => Odd (degree G n))).card

/-- p. 90: `Σ_{e ∈ E} a_ne x_e`, the sum of `x_e` over the edges meeting node `n`. -/
noncomputable def incidentSum {α : Type} [AddCommMonoid α] (G : Graph V E) (x : E → α) (n : V) :
    α :=
  ∑ e ∈ Finset.univ.filter (fun e => n ∈ G.ends e), x e

/-- p. 91, (3.5): `Σ{x_e : e meets S}`. -/
noncomputable def cutSum {α : Type} [AddCommMonoid α] (G : Graph V E) (x : E → α)
    (S : Finset V) : α :=
  ∑ e ∈ Finset.univ.filter (fun e => Meets G e S), x e

/-- p. 93: the real points `x` with integer coordinates satisfying (3.1) `x_e` integer,
(3.2) `x_e ≥ 0` and (3.6) `Σ_e a_ne x_e ≡ b_n (mod 2)` for every node `n`. -/
def parityPoints (G : Graph V E) : Set (E → ℝ) :=
  {x | ∃ z : E → ℤ, (∀ e, 0 ≤ z e) ∧ (∀ n, incidentSum G z n ≡ bParity G n [ZMOD 2]) ∧
    x = fun e => (z e : ℝ)}

/-- p. 94: the polyhedron of solutions to (3.2) `x_e ≥ 0` and (3.5)
`Σ{x_e : e meets S} ≥ 1` for every odd set `S`. -/
def postmanPolyhedron (G : Graph V E) : Set (E → ℝ) :=
  {x | (∀ e, 0 ≤ x e) ∧ ∀ S : Finset V, IsOddSet G S → 1 ≤ cutSum G x S}

/-- p. 94: the odd sets of `G`, which index the dual variables `y_S`. -/
noncomputable def oddSets (G : Graph V E) : Finset (Finset V) :=
  Finset.univ.filter (IsOddSet G)

/-- p. 94, (3.8): `Σ{y_S : S odd, e meets S}`. Only odd sets enter. -/
noncomputable def dualLoad (G : Graph V E) (y : Finset V → ℝ) (e : E) : ℝ :=
  ∑ S ∈ (oddSets G).filter (fun S => Meets G e S), y S

/-- p. 94, (3.9): the dual objective `v = Σ{y_S : S odd}`. -/
noncomputable def dualValue (G : Graph V E) (y : Finset V → ℝ) : ℝ :=
  ∑ S ∈ oddSets G, y S

/-- p. 94: `y` is feasible for the dual problem, (3.7) `y_S ≥ 0` for every odd set `S` and
(3.8) `Σ{y_S : e meets S} ≤ c_e` for every edge `e`. Values of `y` on non-odd sets are ignored. -/
def IsDualFeasible (G : Graph V E) (c : E → ℝ) (y : Finset V → ℝ) : Prop :=
  (∀ S ∈ oddSets G, 0 ≤ y S) ∧ ∀ e, dualLoad G y e ≤ c e

/-- (3.4): the objective `z = Σ_e c_e x_e`. -/
def objective (c x : E → ℝ) : ℝ :=
  ∑ e, c e * x e

/-- p. 91: the integer points `(x, w)` satisfying (3.1), (3.1′), (3.2), (3.2′) and (3.3)
`Σ_e a_ne x_e − 2 w_n = b_n`, read in `ℝ^E × ℝ^N`. -/
def wParityPoints (G : Graph V E) : Set ((E → ℝ) × (V → ℝ)) :=
  {p | ∃ z : E → ℤ, ∃ u : V → ℤ, (∀ e, 0 ≤ z e) ∧ (∀ n, 0 ≤ u n) ∧
    (∀ n, incidentSum G z n - 2 * u n = bParity G n) ∧
    p = (fun e => (z e : ℝ), fun n => (u n : ℝ))}

/-- p. 91: the Chinese postman polyhedron in `(x, w)`, the solutions to (3.2), (3.2′), (3.3) and
(3.5). -/
def wPostmanPolyhedron (G : Graph V E) : Set ((E → ℝ) × (V → ℝ)) :=
  {p | (∀ e, 0 ≤ p.1 e) ∧ (∀ n, 0 ≤ p.2 n) ∧
    (∀ n, incidentSum G p.1 n - 2 * p.2 n = (bParity G n : ℝ)) ∧
    ∀ S : Finset V, IsOddSet G S → 1 ≤ cutSum G p.1 S}

end ChinesePostman.Polyhedron
