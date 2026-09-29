import Mathlib
import Definitions.Def_LocalSearchFL_KMedian_captures

namespace LocalSearchFL.KMedian

/-- Inequality (2) (pp. 550–551). Let `S` be a locally optimum solution for single swaps, `O`
any solution, `σS`, `σO` nearest-facility assignments for `S` and `O` (so `S_j = c_{j σS(j)}`,
`O_j = c_{j σO(j)}`), and `π` a permutation of the clients that maps each `N_O(o)` onto itself
and satisfies Property 3.1 on each. If `s ∈ S`, `o ∈ O` and `s` captures no `o' ∈ O` other than
`o`, then
`∑_{j ∈ N_O(o)} (O_j − S_j) + ∑_{j ∈ N_S(s), j ∉ N_O(o)} (O_j + O_{π(j)} + S_{π(j)} − S_j) ≥ 0`. -/
theorem swap_inequality_2 {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa]
    (I : LocalSearchFL.Shared.MetricInstance Cl Fa) (S O : Finset Fa) (hS : S.Nonempty)
    (hloc : IsSwapLocalOpt I S hS)
    (σS σO : Cl → Fa) (hσS : IsNearestAssignment I S σS) (hσO : IsNearestAssignment I O σO)
    (π : Equiv.Perm Cl) (hπO : ∀ j, σO (π j) = σO j)
    (hπ : ∀ s o : Fa, ¬ captures σS σO s o →
      ∀ j ∈ nbhd σO o ∩ nbhd σS s, π j ∉ nbhd σO o ∩ nbhd σS s)
    (s o : Fa) (hs : s ∈ S) (ho : o ∈ O)
    (hcap : ∀ o' ∈ O, o' ≠ o → ¬ captures σS σO s o') :
    0 ≤ ∑ j ∈ nbhd σO o, (I.c j (σO j) - I.c j (σS j)) +
      ∑ j ∈ nbhd σS s \ nbhd σO o,
        (I.c j (σO j) + I.c (π j) (σO (π j)) + I.c (π j) (σS (π j)) - I.c j (σS j)) := by sorry

end LocalSearchFL.KMedian

