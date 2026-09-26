import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop

namespace KellyStochasticNetworks

theorem braess_paradox :
    (IsWardropEquilibrium braessIncidenceA (fun _ => (0 : Fin 1)) braessDelayA
        (fun _ => 6) ![3, 3]
      ∧ ∀ r : Fin 2, (∑ j, braessDelayA j (linkFlow braessIncidenceA ![3, 3] j)
            * braessIncidenceA j r) = 83)
  ∧ (IsWardropEquilibrium braessIncidenceB (fun _ => (0 : Fin 1)) braessDelayB
        (fun _ => 6) ![2, 2, 2]
      ∧ ∀ r : Fin 3, (∑ j, braessDelayB j (linkFlow braessIncidenceB ![2, 2, 2] j)
            * braessIncidenceB j r) = 92) := by sorry

end KellyStochasticNetworks
