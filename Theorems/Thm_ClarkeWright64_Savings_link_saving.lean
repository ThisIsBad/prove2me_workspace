import Mathlib
import Definitions.Def_SupplyChainTheory_vrp
import Definitions.Def_ClarkeWright64_Savings_Instance
import Definitions.Def_ClarkeWright64_Savings_Procedure

namespace ClarkeWright64.Savings

/-- Clarke & Wright (1964), Theoretical aspects, pp. 571–572: linking an admissible cell `(y:z)`
of a state reached by the procedure lowers the total mileage by exactly the saving
`d_{0,y} + d_{0,z} − d_{y,z}`, for symmetric distances. -/
theorem link_saving {M n : ℕ} (I : Instance M n) (hsymm : ∀ i j, I.d i j = I.d j i)
    (s : State M) (hs : Reachable I s) (y z : Fin (M + 1)) (hyz : Admissible I s y z) :
    I.mileage (link s y z) = I.mileage s - I.saving y z := by sorry

end ClarkeWright64.Savings

