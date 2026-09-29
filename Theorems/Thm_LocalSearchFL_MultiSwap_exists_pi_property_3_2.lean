import Mathlib

namespace LocalSearchFL.MultiSwap

/-- Property 3.2 (p. 553), in abstract form. Let `N` be a finite set (the clients `N_O(o)` of a
facility `o`) partitioned into the classes of a labelling `g` (the class of `j` is
`P_j = {x ∈ N | g x = g j}`). There is a bijection `π` of `N` (a permutation fixing every point
outside `N`) such that `π(P) ∩ P = ∅` for every class `P` with `|P| ≤ ½ |N|`. -/
theorem exists_pi_property_3_2 {α β : Type} [DecidableEq β] (N : Finset α) (g : α → β) :
    ∃ π : Equiv.Perm α,
      (∀ j, π j ∈ N ↔ j ∈ N) ∧
      (∀ j, j ∉ N → π j = j) ∧
      ∀ j ∈ N, 2 * (N.filter (fun x => g x = g j)).card ≤ N.card → g (π j) ≠ g j := by sorry

end LocalSearchFL.MultiSwap

