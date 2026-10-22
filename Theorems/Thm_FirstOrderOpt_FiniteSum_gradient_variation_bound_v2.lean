import Mathlib


namespace FirstOrderOpt.FiniteSum

/-- Lemma 5.12 (per-component gradient-variation bound), Lan p. 278. In the finite-sum setting
of §5.3, `X ⊆ E` is closed convex, `Ψ = f + h` with `h` convex and `f = (1/m) Σ_i fi` the average
of `m ≥ 1` convex component functions, each differentiable with `Li`-Lipschitz gradient
`gradf i` (the standing smoothness assumption preceding (5.3.3)); `q` is a probability
distribution on `{1, …, m}` and `LQ := (1/m) max_i (Li/qi)` (5.3.4). If `xstar` is an optimal
solution of (5.3.1), then for every `x ∈ X`,
`(1/m) Σ_i (1/(m qi)) ‖gradf i x - gradf i xstar‖² ≤ 2 LQ (Ψ x - Ψ xstar)`.

Corrected version: `gradf i` is the gradient of `fi`, each `fi` is convex, `h` is convex and `X`
is closed convex — the retired statement took `gradf` as a free family of functionals with only a
Lipschitz bound, which carries no co-coercivity. The `fi` are convex and smooth on the whole space,
as in the book (problem (5.3.1) minimizes over `X` functions defined on `ℝⁿ`). -/
theorem gradient_variation_bound_v2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} (hne : (Finset.univ : Finset (Fin m)).Nonempty)
    (X : Set E) (hXconv : Convex ℝ X) (hXclosed : IsClosed X)
    (f h Ψ : E → ℝ) (hΨ : ∀ x, Ψ x = f x + h x) (hhconv : ConvexOn ℝ X h)
    (fi : Fin m → E → ℝ) (hf : ∀ x, f x = (1 / (m : ℝ)) * ∑ i, fi i x)
    (hfi_conv : ∀ i, ConvexOn ℝ Set.univ (fi i))
    (gradf : Fin m → E → E →L[ℝ] ℝ)
    (hgrad : ∀ i x, HasFDerivAt (fi i) (gradf i x) x)
    (L : Fin m → ℝ) (hL : ∀ i, 0 < L i)
    (hsmooth : ∀ i x y, ‖gradf i x - gradf i y‖ ≤ L i * ‖x - y‖)
    (q : Fin m → ℝ) (hq_pos : ∀ i, 0 < q i) (hq_sum : ∑ i, q i = 1)
    (LQ : ℝ) (hLQ : LQ = (1 / (m : ℝ)) * Finset.univ.sup' hne (fun i => L i / q i))
    (xstar : E) (hxstar : xstar ∈ X) (hxstar_opt : ∀ y ∈ X, Ψ xstar ≤ Ψ y) :
    ∀ x ∈ X, (1 / (m : ℝ)) * ∑ i, (1 / ((m : ℝ) * q i)) * ‖gradf i x - gradf i xstar‖ ^ 2 ≤
      2 * LQ * (Ψ x - Ψ xstar) := by sorry

end FirstOrderOpt.FiniteSum

