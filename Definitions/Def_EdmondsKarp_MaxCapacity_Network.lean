import Mathlib

namespace EdmondsKarp.MaxCapacity

/-- A network in the sense of Edmonds–Karp (1972), §1.1, p. 249: a finite node set `V`, a source `s`,
a sink `t`, the set `A` of all arcs *except* the return arc `(t, s)` (a set of ordered pairs, so at most
one arc from a node to another; no loops), and a capacity `c u v > 0` on every arc of `A`. Capacities are
real numbers. Values of `c` off `A` are irrelevant. -/
structure Network (V : Type) [Fintype V] [DecidableEq V] where
  s : V
  t : V
  source_ne_sink : s ≠ t
  A : Finset (V × V)
  no_loop : ∀ p ∈ A, p.1 ≠ p.2
  return_not_mem : (t, s) ∉ A
  c : V → V → ℝ
  cap_pos : ∀ p ∈ A, 0 < c p.1 p.2

variable {V : Type} [Fintype V] [DecidableEq V]

/-- All arcs of `N`: the arcs of `A` together with the return arc `(t, s)`. -/
def Network.arcs (N : Network V) : Finset (V × V) := insert (N.t, N.s) N.A

/-- A flow in `N` (§1.1, p. 249): a function `f u v`, meaningful on the arcs of `N` (values off the
arcs are ignored), which is nonnegative on every arc of `N` (including the return arc),
(i) at most the capacity on every arc of `A`, and (ii) conserves flow at every node `u`,
the sums running over the arcs of `N` leaving resp. entering `u`. -/
def IsFlow (N : Network V) (f : V → V → ℝ) : Prop :=
  (∀ u v, (u, v) ∈ N.arcs → 0 ≤ f u v) ∧
  (∀ u v, (u, v) ∈ N.A → f u v ≤ N.c u v) ∧
  (∀ u, (∑ v ∈ Finset.univ.filter (fun v => (u, v) ∈ N.arcs), f u v) -
      (∑ v ∈ Finset.univ.filter (fun v => (v, u) ∈ N.arcs), f v u) = 0)

/-- A maximum flow (§1.1, p. 249): a flow `f` whose return-arc value `f(t, s)` is at least `g(t, s)`
for every flow `g` in `N`. -/
def IsMaxFlow (N : Network V) (f : V → V → ℝ) : Prop :=
  IsFlow N f ∧ ∀ g : V → V → ℝ, IsFlow N g → g N.t N.s ≤ f N.t N.s

/-- Every capacity of `N` is an integer (§1.3, p. 253: "a network in which every capacity is an
integer"). -/
def IntegralCaps (N : Network V) : Prop :=
  ∀ p ∈ N.A, ∃ z : ℤ, N.c p.1 p.2 = z

/-- The function `f` is integer-valued on the arcs of `N` (including the return arc) (p. 250). -/
def IsIntegralOn (N : Network V) (f : V → V → ℝ) : Prop :=
  ∀ p ∈ N.arcs, ∃ z : ℤ, f p.1 p.2 = z

end EdmondsKarp.MaxCapacity
