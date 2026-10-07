import Mathlib
import Definitions.Def_ConvexOptAlg_Ellipsoid_Defs

namespace ConvexOptAlg.Ellipsoid

/-- The remark before Theorem 2.4 (Bubeck, arXiv:1405.4980v2, §2.2, p. 250): at step `t` of the
ellipsoid method a point of `X` can be removed from the current ellipsoid only if `c_t ∈ X`, and
then (as in (2.2), p. 246) its value exceeds `f(c_t)`. Formally: in a run with `n ≥ 2`, `R > 0`
and nonzero oracle answers `w_0, …, w_t`, every `x ∈ X` lying in `E_t` but not in `E_{t+1}`
satisfies `c_t ∈ X` and `f(c_t) < f(x)`, where
`E_s = {x : (x − c_s)⊤H_s⁻¹(x − c_s) ≤ 1}`. -/
theorem cut_keeps_X {n : ℕ} (hn : 2 ≤ n) (X : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (R : ℝ) (hR : 0 < R) (c0 : Fin n → ℝ) (c : ℕ → Fin n → ℝ)
    (H : ℕ → Matrix (Fin n) (Fin n) ℝ) (w : ℕ → Fin n → ℝ)
    (hrun : IsEllipsoidRun X f R c0 c H w) (t : ℕ) (hw : ∀ s ≤ t, w s ≠ 0)
    (x : Fin n → ℝ) (hxX : x ∈ X) (hxt : x ∈ LinearOptimization.ellipsoid (c t) (H t))
    (hxt1 : x ∉ LinearOptimization.ellipsoid (c (t + 1)) (H (t + 1))) :
    c t ∈ X ∧ f (c t) < f x := by sorry

end ConvexOptAlg.Ellipsoid

