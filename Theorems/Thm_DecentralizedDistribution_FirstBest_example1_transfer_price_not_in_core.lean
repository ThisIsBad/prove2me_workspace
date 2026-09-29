import Mathlib
import Definitions.Def_Supermodularity_Cooperative_Core
import Definitions.Def_DecentralizedDistribution_FirstBest_System

open Supermodularity.Cooperative

namespace DecentralizedDistribution.FirstBest

/-- Example 1 (p. 358). Four retailers, no warehouses, `r_n = 10`, `v_n = 5`, `t_{i,n} = 1`,
`β_{i,n} = 1`; stocks `X = (3, 1, 0, 0)` and demands `D = (0, 0, 5, 2)`, so that
`H_1 = 3, H_2 = 1, E_3 = 5, E_4 = 2` (all other residuals zero). Then `W*_𝒩 = 16`, the coalition
`{1, 4}` (indices `0, 3`) has `W*_{{1,4}} = 8`, and the transfer-price allocation `(0, 0, 16, 0)`
is not in the core of SAG([Z], D⃗). -/
theorem example1_transfer_price_not_in_core (sys : System 4 0)
    (hr : ∀ n, sys.r n = 10) (hv : ∀ n, sys.v n = 5)
    (ht : ∀ i n, sys.t i n = 1) (hβ : ∀ i n, sys.β i n = 1)
    (Z : Profile 4 0) (hX : (fun n => (Z n).X) = ![3, 1, 0, 0])
    (D : Demand 4) (hD : D = ![0, 0, 5, 2]) :
    coalitionValue sys Finset.univ Z D = 16 ∧
    coalitionValue sys {0, 3} Z D = 8 ∧
    (![0, 0, 16, 0] : Fin 4 → ℝ) ∉ Core Finset.univ (fun S => coalitionValue sys S Z D) := by sorry

end DecentralizedDistribution.FirstBest
