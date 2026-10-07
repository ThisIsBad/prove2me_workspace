import Mathlib
import Definitions.Def_CachonCoord_TwoLocation_Model

open MeasureTheory

namespace CachonCoord.TwoLocation

/-- §6.8.4, p. 83, Eqs. (35)–(37). The partial derivatives of the supply chain's cost are
(35) `∂Π/∂s_r = F_s(s_s) c'(s_r) + ∫_{s_s}^∞ c'(s_r + s_s − x) f_s(x) dx` and
(36) `∂Π/∂s_s = F_s(s_s) h_s + ∫_{s_s}^∞ c'(s_r + s_s − x) f_s(x) dx`
(the integrals against `f_s(x) dx` written as integrals against the law of `D_s` over
`(s_s, ∞)`); every optimal policy with `s_s > 0` has `c'(s_r) = h_s` (37), i.e.
`F_r(s_r) = (h_s + β)/(h_r + β)`; the solution `s̃¹_r` of that equation exists and is unique, and
then `∂Π(s̃¹_r, s_s)/∂s_s = 0` has exactly one solution `s̃¹_s`. -/
theorem eq_35_37 (M : Model) :
    (∀ sr ss : ℝ, HasDerivAt (fun x => M.Pi x ss)
      (M.FS ss * M.cDeriv sr + ∫ x in Set.Ioi ss, M.cDeriv (sr + ss - x) ∂M.lawS) sr) ∧
    (∀ sr ss : ℝ, HasDerivAt (fun y => M.Pi sr y)
      (M.FS ss * M.hs + ∫ x in Set.Ioi ss, M.cDeriv (sr + ss - x) ∂M.lawS) ss) ∧
    (∀ sr ss : ℝ, IsMinOn (fun p : ℝ × ℝ => M.Pi p.1 p.2) Set.univ (sr, ss) → 0 < ss →
      M.cDeriv sr = M.hs ∧ M.FR sr = (M.hs + M.beta) / (M.hr + M.beta)) ∧
    (∃! s1r : ℝ, M.FR s1r = (M.hs + M.beta) / (M.hr + M.beta)) ∧
    (∀ s1r : ℝ, M.FR s1r = (M.hs + M.beta) / (M.hr + M.beta) →
      ∃! s1s : ℝ, M.FS s1s * M.hs + ∫ x in Set.Ioi s1s, M.cDeriv (s1r + s1s - x) ∂M.lawS = 0) := by sorry

end CachonCoord.TwoLocation

