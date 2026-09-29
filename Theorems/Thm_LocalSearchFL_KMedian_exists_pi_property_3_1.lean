import Mathlib
import Definitions.Def_LocalSearchFL_KMedian_captures

namespace LocalSearchFL.KMedian

/-- Property 3.1 (p. 549): for a facility `o`, there is a bijection `π` of `N_O(o)` (a
permutation of the clients that fixes every client outside `N_O(o)`) such that, for every
facility `s` that does not capture `o`, `π(N^o_s) ∩ N^o_s = ∅`. -/
theorem exists_pi_property_3_1 {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa]
    (σS σO : Cl → Fa) (o : Fa) :
    ∃ π : Equiv.Perm Cl,
      (∀ j, π j ∈ nbhd σO o ↔ j ∈ nbhd σO o) ∧
      (∀ j, j ∉ nbhd σO o → π j = j) ∧
      ∀ s : Fa, ¬ captures σS σO s o →
        ∀ j ∈ nbhd σO o ∩ nbhd σS s, π j ∉ nbhd σO o ∩ nbhd σS s := by sorry

end LocalSearchFL.KMedian
