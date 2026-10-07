import Mathlib
import Definitions.Def_MechanismDesign_Auctions_Model

open MeasureTheory

namespace MechanismDesign.Auctions

/-- Lemma 3.2, p.37: in an incentive-compatible direct mechanism every interim utility `U_i` is
increasing and convex on `[θ̲, θ̄]`, differentiable at all but countably many interior points,
and `U_i'(θ_i) = Q_i(θ_i)` wherever it is differentiable. -/
theorem interimU_envelope {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Environment ι}
    (m : DirectMechanism E) (hIC : m.IsIC) (i : ι) :
    MonotoneOn (m.interimU i) (Set.Icc E.lo E.hi) ∧
    ConvexOn ℝ (Set.Icc E.lo E.hi) (m.interimU i) ∧
    {x | x ∈ Set.Ioo E.lo E.hi ∧ ¬ DifferentiableAt ℝ (m.interimU i) x}.Countable ∧
    ∀ x ∈ Set.Ioo E.lo E.hi, DifferentiableAt ℝ (m.interimU i) x →
      deriv (m.interimU i) x = m.interimQ i x := by sorry

end MechanismDesign.Auctions

