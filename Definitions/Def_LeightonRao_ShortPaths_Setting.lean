import Mathlib
import Definitions.Def_LeightonRao_ShortPaths_Network

namespace LeightonRao.ShortPaths

variable {V : Type} [Fintype V] [DecidableEq V]

noncomputable def totalCap (N : Network V) : ℝ :=
  (1 / 2 : ℝ) * ∑ u, ∑ v, N.C u v

/-- Largest total capacity incident to one vertex. The empty-type default is irrelevant to results. -/
noncomputable def cmax (N : Network V) : ℝ :=
  sSup (Set.range fun v : V => ∑ u, N.C v u)

def IsDistanceFunction (d : V → V → ℝ) : Prop :=
  (∀ u v, 0 ≤ d u v) ∧ (∀ u v, d u v = d v u)

noncomputable def totalWeight (N : Network V) (d : V → V → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ u, ∑ v, N.C u v * d u v

def walkLen {N : Network V} (d : V → V → ℝ) {u v : V} (p : N.graph.Walk u v) : ℝ :=
  (p.darts.map fun a => d a.fst a.snd).sum

/-- Infimum of lengths of walks using at most `B` edges. An empty walk family gives `⊤`. -/
noncomputable def distL (N : Network V) (d : V → V → ℝ) (B : ℝ) (u v : V) : ENNReal :=
  ⨅ (p : N.graph.Walk u v) (_ : (p.length : ℝ) ≤ B), ENNReal.ofReal (walkLen d p)

noncomputable def distFromL (N : Network V) (d : V → V → ℝ) (B : ℝ)
    (T : Finset V) (u : V) : ENNReal :=
  ⨅ t ∈ T, distL N d B t u

def SatisfiesShortConstraint (N : Network V) (d : V → V → ℝ) (L : ℕ) : Prop :=
  1 ≤ (1 / 2 : ENNReal) * ∑ u, ∑ v, distL N d (L : ℝ) u v

/-- One walk within the component witnesses both the hop radius and the distance radius. -/
def HasRadii (N : Network V) (d : V → V → ℝ) (S : Finset V) (ρe ρd : ℝ) : Prop :=
  ∃ c ∈ S, ∀ y ∈ S, ∃ p : N.graph.Walk c y,
    (∀ x ∈ p.support, x ∈ S) ∧ (p.length : ℝ) ≤ ρe ∧ walkLen d p ≤ ρd

noncomputable def crossCap (N : Network V) (P : Finpartition (Finset.univ : Finset V)) : ℝ :=
  (1 / 2 : ℝ) * ∑ u, ∑ v, if P.part u = P.part v then 0 else N.C u v

/-- Hop-indexed concurrent flow. `f s t h i j` is commodity `s,t` on `i → j` at hop `h+1`.
The equations inject flow at hop zero, conserve it at each later hop, absorb it at the sink,
and forbid flow after hop `L`; hence every routed path has at most `L` edges. -/
def IsShortConcurrentFlow (N : Network V) (D : V → V → ℝ) (L : ℕ)
    (f : V → V → ℕ → V → V → ℝ) (lam : ℝ) : Prop :=
  (∀ s t h i j, 0 ≤ f s t h i j) ∧
  (∀ s t h i j, L ≤ h → f s t h i j = 0) ∧
  (∀ s h i j, f s s h i j = 0) ∧
  (∀ s t, s ≠ t → ∀ v, ∑ j, f s t 0 v j = if v = s then lam * D s t else 0) ∧
  (∀ s t h, s ≠ t → h + 1 < L → ∀ v,
    ∑ j, f s t (h + 1) v j = if v = t then 0 else ∑ i, f s t h i v) ∧
  (∀ s t h, s ≠ t → h < L → ∑ j, f s t h t j = 0) ∧
  (∀ s t h, s ≠ t → h + 1 = L → ∀ v, v ≠ t → ∑ i, f s t h i v = 0) ∧
  (∀ s t, s ≠ t → ∑ h ∈ Finset.range L, ∑ i, f s t h i t = lam * D s t) ∧
  (∀ i j, ∑ s, ∑ t, ∑ h ∈ Finset.range L,
    (f s t h i j + f s t h j i) ≤ N.C i j)

/-- Concurrent short-path max-flow, as a supremum of feasible values. -/
noncomputable def maxShortFlow (N : Network V) (D : V → V → ℝ) (L : ℕ) : ℝ :=
  sSup {lam : ℝ | 0 ≤ lam ∧ ∃ f, IsShortConcurrentFlow N D L f lam}

end LeightonRao.ShortPaths
