import Mathlib
import Definitions.Def_LovaszSchrijver_NPlus_Constraints

namespace LovaszSchrijver.NPlus

theorem contraction_support_bipartite {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : ∀ v, ∃ w, G.Adj v w) :
    (∀ B : Finset V, G.IsClique (B : Set V) → 3 ≤ B.card → ∀ v, 0 < chi B v →
        (G.induce {w | 0 < contractCoeff G (chi B) v w}).Colorable 2) ∧
    (∀ C : Finset V, IsOddHole G C → ∀ v, 0 < chi C v →
        (G.induce {w | 0 < contractCoeff G (chi C) v w}).Colorable 2) ∧
    (∀ U : Finset V, ∀ u₀ : V, IsOddWheel G U u₀ → ∀ v, 0 < wheelCoeff U u₀ v →
        (G.induce {w | 0 < contractCoeff G (wheelCoeff U u₀) v w}).Colorable 2) ∧
    (∀ D : Finset V, IsOddAntihole G D → ∀ v, 0 < chi D v →
        (G.induce {w | 0 < contractCoeff G (chi D) v w}).Colorable 2) := by sorry

end LovaszSchrijver.NPlus

