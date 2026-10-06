import Mathlib
import Definitions.Def_BregmanRelax_Cyclic_DConditions

namespace BregmanRelax.Remotest

/-- The remotest-set control of Theorem 2 (p. 203): at every step the chosen index `i n`
realizes `max_j min_{z ∈ A j} D z (x n)`. By condition II the inner minimum (over `A j ∩ S`,
where `D` is defined) is attained at the D-projection, so it equals `D (P j (x n)) (x n)`. -/
def IsRemotestControl {X : Type*} {ι : Type*} (D : X → X → ℝ) (P : ι → X → X) (i : ℕ → ι)
    (x : ℕ → X) : Prop :=
  ∀ n, ∀ j, D (P j (x n)) (x n) ≤ D (P (i n) (x n)) (x n)

end BregmanRelax.Remotest
