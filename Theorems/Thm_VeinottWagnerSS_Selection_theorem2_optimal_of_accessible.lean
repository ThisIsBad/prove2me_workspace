import Mathlib
import Definitions.Def_VeinottWagnerSS_Selection_Model
import Definitions.Def_VeinottWagnerSS_Selection_CandidateSet

namespace VeinottWagnerSS.Selection

/-- Veinott & Wagner (1965), Theorem 2, p. 543: let `0 < α < 1` and let `(sⁱ, Sⁱ)`, `(sʲ, Sʲ)`
be policies of the candidate set `𝒮` of Step ii. If `(sⁱ, Sⁱ)` is optimal, and if each `x'`
with `min(sⁱ, sʲ) ≤ x' < max(sⁱ, sʲ)` is accessible from `Sʲ` under `(sʲ, Sʲ)`, then
`(sʲ, Sʲ)` is optimal. -/
theorem theorem2_optimal_of_accessible (M : Model) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (pi pj : ℤ × ℤ) (hpi : pi ∈ candSet M α) (hpj : pj ∈ candSet M α)
    (hopt : Optimal M α pi.1 pi.2)
    (hacc : ∀ x' : ℤ, min pi.1 pj.1 ≤ x' → x' < max pi.1 pj.1 →
      Accessible M pj.1 pj.2 pj.2 x') :
    Optimal M α pj.1 pj.2 := by sorry

end VeinottWagnerSS.Selection

