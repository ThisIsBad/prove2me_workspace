import Mathlib
import Definitions.Def_RobustGeneralization_BernUpper_Model

namespace RobustGeneralization.BernUpper

/-- Schmidt et al., arXiv:1804.11285v2, §2.2, p. 7, the sentence after the definition of `T`:
for `ε < 1` the thresholding operator undoes any ℓ∞-bounded adversary, `T(B∞^ε(x)) = {x}` for
every `x ∈ {±1}^d`. The hypothesis `0 ≤ ε` is added: for `ε < 0` the ball is empty. -/
theorem threshold_undoes_linf_adversary {d : ℕ} (s : Fin d → Bool) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    thr '' linfBall (pm s) ε = {pm s} := by sorry

end RobustGeneralization.BernUpper
