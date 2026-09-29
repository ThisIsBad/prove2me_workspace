import Mathlib
import Definitions.Def_ChvatalPolytopes_Perfect_StablePolytope
import Definitions.Def_ChvatalPolytopes_Perfect_IsPerfect

namespace ChvatalPolytopes.Perfect

/-- **Lovász's first theorem** (cited in Chvátal 1975, §3, p. 140, from Lovász [16]): every
nonperfect graph `G` (in the sense of `IsPerfect`, the paper's α-perfection) contains an induced
subgraph `G_A` with `α(G_A) · ω(G_A) < |A|`. Here `α = indepNum`, `ω = cliqueNum` (Mathlib,
ℕ-valued) and `G_A = G.induce A`. -/
theorem exists_induced_indepNum_mul_cliqueNum_lt {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : ¬ IsPerfect G) :
    ∃ A : Finset V,
      (G.induce (A : Set V)).indepNum * (G.induce (A : Set V)).cliqueNum < A.card := by sorry

end ChvatalPolytopes.Perfect

