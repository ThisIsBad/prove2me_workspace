import Mathlib
import Definitions.Def_LocalSearchFL_UFL_captures

namespace LocalSearchFL.UFL

/-- Inequality (5), p. 555. Let `S` be a locally optimum solution for the neighbourhood (4), `O`
any solution, `σS`, `σO` nearest-facility assignments for `S` and `O` (so `S_j = c_{j σS(j)}`,
`O_j = c_{j σO(j)}`), and `π` the mapping of the proof of Lemma 4.2. If there is at least one
client and `s ∈ S` is good (captures no `o ∈ O`), then
`−f_s + ∑_{j ∈ N_S(s), π(j) ≠ j} (O_j + O_{π(j)} + S_{π(j)} − S_j)
  + 2 ∑_{j ∈ N_S(s), π(j) = j} O_j ≥ 0`. -/
theorem drop_good_inequality_5 {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [Nonempty Cl]
    [Fintype Fa] [DecidableEq Fa]
    (I : MetricInstance Cl Fa) (f : Fa → ℝ) (hf : ∀ i, 0 ≤ f i)
    (S O : Finset Fa) (hS : S.Nonempty) (hloc : IsUFLLocalOpt I f S hS)
    (σS σO : Cl → Fa) (hσS : IsNearestAssignment I S σS) (hσO : IsNearestAssignment I O σO)
    (π : Equiv.Perm Cl) (hπ : IsRefinedPi σS σO π)
    (s : Fa) (hs : s ∈ S) (hgood : IsGood σS σO O s) :
    0 ≤ -f s +
      ∑ j ∈ (nbhd σS s).filter (fun j => π j ≠ j),
        (I.c j (σO j) + I.c (π j) (σO (π j)) + I.c (π j) (σS (π j)) - I.c j (σS j)) +
      2 * ∑ j ∈ (nbhd σS s).filter (fun j => π j = j), I.c j (σO j) := by sorry

end LocalSearchFL.UFL
