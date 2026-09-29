import Mathlib
import Definitions.Def_LocalSearchFL_CFL_MetricInstance

namespace LocalSearchFL.CFL

/-- A **solution of the capacitated facility location problem** (∞-CFL, §2 p. 547 and §5
p. 558) for capacities `u : Fa → ℕ`: a multiset of facility copies together with an assignment
of clients to copies respecting the capacities. There are `n` open copies, indexed by `Fin n`;
copy `s` is a copy of facility `loc s`; client `j` is served by copy `σ j`; and each copy `s`
serves at most `u (loc s)` clients. Several copies of the same facility may be open. -/
structure CFLSol (Cl Fa : Type) [Fintype Cl] (u : Fa → ℕ) where
  /-- The number of open copies. -/
  n : ℕ
  /-- The facility of which copy `s` is a copy. -/
  loc : Fin n → Fa
  /-- The copy serving client `j`. -/
  σ : Cl → Fin n
  /-- Capacity: copy `s` serves at most `u (loc s)` clients. -/
  cap : ∀ s, (Finset.univ.filter (fun j => σ j = s)).card ≤ u (loc s)

variable {Cl Fa : Type} [Fintype Cl] {u : Fa → ℕ}

/-- The multiset of facilities opened by `X` (each facility with its number of copies). -/
def CFLSol.facMultiset (X : CFLSol Cl Fa u) : Multiset Fa :=
  Multiset.map X.loc Finset.univ.val

/-- `N_X(s)`: the set of clients served by the copy `s` of `X`. -/
def CFLSol.nbhd (X : CFLSol Cl Fa u) (s : Fin X.n) : Finset Cl :=
  Finset.univ.filter (fun j => X.σ j = s)

/-- `N_X(T) = ⋃_{s ∈ T} N_X(s)`: the set of clients served by the copies in `T`. -/
def CFLSol.nbhdSet (X : CFLSol Cl Fa u) (T : Finset (Fin X.n)) : Finset Cl :=
  Finset.univ.filter (fun j => X.σ j ∈ T)

/-- The **facility cost** `cost_f(X) = ∑_{s ∈ X} f_s`, one term per open copy. -/
def costF (f : Fa → ℝ) (X : CFLSol Cl Fa u) : ℝ :=
  ∑ s : Fin X.n, f (X.loc s)

/-- The **service cost** `cost_s(X) = ∑_{j ∈ C} c_{j σ(j)}` of `X` under its assignment `σ`. -/
def costS (I : MetricInstance Cl Fa) (X : CFLSol Cl Fa u) : ℝ :=
  ∑ j : Cl, I.c j (X.loc (X.σ j))

/-- The **cost** `cost(X) = ∑_{i ∈ S} f_i + ∑_{j ∈ C} c_{j σ(j)}` (§5, p. 558). -/
def cost (I : MetricInstance Cl Fa) (f : Fa → ℝ) (X : CFLSol Cl Fa u) : ℝ :=
  costF f X + costS I X

end LocalSearchFL.CFL
