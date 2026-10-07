import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_mm_continuous
import Definitions.Def_LogSobolevMC_Entropy_Setting

namespace LogSobolevMC.Entropy

theorem lemma_2_5_ent {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : MarkovMixing.IsStochastic K)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary K π) (hπpos : ∀ x, 0 < π x)
    (f : V → ℝ) (hf : ∀ x, 0 < f x) :
    HasDerivAt (fun t : ℝ => entF π (LogSobolevMC.ChiSquare.heatOp K t f))
      (-LogSobolevMC.ChiSquare.dirichlet K π f (fun x => Real.log (f x))) 0 := by sorry

end LogSobolevMC.Entropy

