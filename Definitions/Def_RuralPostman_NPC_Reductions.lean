import Mathlib
import Definitions.Def_RuralPostman_NPC_Instances

namespace RuralPostman.NPC

/-! # The two constructions of §2 (pp. 5–6)

From a graph `H = (V, E)` on `V = Fin v`, the rural postman instance on `N = V × {0,1}`, encoded
as `Fin (v + v)`: node `⟨s,0⟩` is `Fin.castAdd v s` and node `⟨s,1⟩` is `Fin.natAdd v s`. -/

/-- The undirected construction (p. 5–6): for each `s ∈ V` the required arc `(⟨s,0⟩, ⟨s,1⟩)` of
weight `0`; for each edge `{s, t}` of `H` (listed once, as `s < t` with `adj s t = true`) the
non-required arc `(⟨s,0⟩, ⟨t,0⟩)` of weight `1`; and `k = v`. -/
def urpOfGraph {v : ℕ} (adj : Fin v → Fin v → Bool) : RPInstance where
  n := v + v
  arcs :=
    (List.finRange v).map (fun s => (Fin.castAdd v s, Fin.natAdd v s, 0, true)) ++
    (List.finRange v).flatMap (fun s =>
      ((List.finRange v).filter (fun t => decide (s < t) && adj s t)).map
        (fun t => (Fin.castAdd v s, Fin.castAdd v t, 1, false)))
  k := v

/-- The directed construction (p. 6): for each `s ∈ V` the required arc `(⟨s,0⟩, ⟨s,1⟩)` and the
non-required arc `(⟨s,1⟩, ⟨s,0⟩)`, both of weight `0`; for each arc `(s, t)` of `H`
(`adj s t = true`) the non-required arc `(⟨s,0⟩, ⟨t,0⟩)` of weight `1`; and `k = v`. -/
def drpOfGraph {v : ℕ} (adj : Fin v → Fin v → Bool) : RPInstance where
  n := v + v
  arcs :=
    (List.finRange v).flatMap (fun s =>
      [(Fin.castAdd v s, Fin.natAdd v s, 0, true), (Fin.natAdd v s, Fin.castAdd v s, 0, false)]) ++
    (List.finRange v).flatMap (fun s =>
      ((List.finRange v).filter (fun t => adj s t)).map
        (fun t => (Fin.castAdd v s, Fin.castAdd v t, 1, false)))
  k := v

end RuralPostman.NPC
