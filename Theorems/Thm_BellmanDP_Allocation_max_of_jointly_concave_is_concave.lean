import Mathlib

namespace BellmanDP.Allocation

/-- Ch. I, Lemma 1, p. 21. If `G(x, y)` is concave jointly in `(x, y)` on `x, y ≥ 0` and
`f(x) = Max_{0 ≤ y ≤ x} G(x, y)` (the maximum being attained for every `x ≥ 0`), then `f` is
concave on `x ≥ 0`. -/
theorem max_of_jointly_concave_is_concave (G : ℝ → ℝ → ℝ)
    (hG : ConcaveOn ℝ (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ)) (fun p : ℝ × ℝ => G p.1 p.2))
    (f : ℝ → ℝ) (hf : ∀ x : ℝ, 0 ≤ x → IsGreatest ((G x) '' Set.Icc 0 x) (f x)) :
    ConcaveOn ℝ (Set.Ici 0) f := by sorry

end BellmanDP.Allocation

