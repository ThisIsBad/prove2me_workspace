import Mathlib
import Definitions.Def_OnlineRandomization_Restart_Model
import Definitions.Def_OnlineRandomization_Restart_GameProperties
import Definitions.Def_OnlineRandomization_Restart_RestartAlgorithm

namespace OnlineRandomization.Restart

/-- §4, proof of Theorem 4.1, p. 17: by locality (and finiteness of the request set `R`),
`R_H` is a finite set, for every real `H`. -/
theorem rh_finite {R A : Type*} [Finite R] [Fintype A] [Nonempty A] (F : Game R A)
    (hloc : IsLocal F) (H : ℝ) :
    {r : List R | InRH F H r}.Finite := by sorry

end OnlineRandomization.Restart

