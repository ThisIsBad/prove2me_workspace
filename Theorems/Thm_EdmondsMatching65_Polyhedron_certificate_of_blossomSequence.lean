import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_EdmondsMatching65_Polyhedron_DualProgram
import Definitions.Def_EdmondsMatching65_Polyhedron_BlossomSequence

namespace EdmondsMatching65.Polyhedron

theorem certificate_of_blossomSequence {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : Graph V E) (c : E → ℝ) (M : Finset E)
    (hM : IsMatching G M) (s : BlossomSequence G c M) :
    ∃ (y : V → ℝ) (z : Finset V → ℝ), DualFeasible G c y z ∧ CompSlack G c M y z := by sorry

end EdmondsMatching65.Polyhedron

