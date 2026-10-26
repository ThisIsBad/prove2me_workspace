import Mathlib
import Definitions.Def_StoneRegression_Criterion_Setting

namespace StoneRegression.Quantile

open MeasureTheory ProbabilityTheory

/-- The conditional distribution function `F^Y(y | X = x) = P^Y((−∞, y] | X = x)` (§7, p. 603), where the
Markov kernel `κ` is the conditional law of `Y` given `X`. For a Markov kernel it is nondecreasing and
right-continuous in `y`, with limits `0` at `−∞` and `1` at `+∞`. -/
noncomputable def condCdf {d : ℕ} (κ : Kernel (EuclideanSpace ℝ (Fin d)) ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (y : ℝ) : ℝ :=
  (κ x (Set.Iic y)).toReal

/-- The lower `p`th conditional quantile `L^Y(p | X = x) = inf [y : F^Y(y | X = x) ≥ p]` (§7, p. 603).
For a Markov kernel `κ` and `0 < p < 1` the set is nonempty (the CDF tends to `1 > p`) and bounded
below (the CDF tends to `0 < p`), so the real `sInf` is the page's infimum (and is attained, by right
continuity). Outside `0 < p < 1` the value is not used. -/
noncomputable def lowerQ {d : ℕ} (κ : Kernel (EuclideanSpace ℝ (Fin d)) ℝ) (p : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  sInf {y : ℝ | p ≤ condCdf κ x y}

/-- The upper `p`th conditional quantile `U^Y(p | X = x) = sup [y : F^Y(y | X = x) ≤ p]` (§7, p. 603).
For a Markov kernel `κ` and `0 < p < 1` the set is nonempty (the CDF tends to `0 < p`) and bounded
above (the CDF tends to `1 > p`), so the real `sSup` is the page's supremum. -/
noncomputable def upperQ {d : ℕ} (κ : Kernel (EuclideanSpace ℝ (Fin d)) ℝ) (p : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  sSup {y : ℝ | condCdf κ x y ≤ p}

/-- The weighted empirical conditional distribution function
`F̂ₙ^Y(y | X) = P̂ₙ^Y((−∞, y] | X) = ∑ᵢ W_{ni}(X) I{Yᵢ ≤ y}` (§7, p. 603), on a path `ω` of the pairs
`(X, Y), (X₁, Y₁), …` (coordinate `0` is `(X, Y)`, coordinate `i+1` is `(X_{i+1}, Y_{i+1})`; the StoneRegression.Criterion.sample
index is 0-based). -/
noncomputable def estCdf {d : ℕ} (W : StoneRegression.Criterion.WeightSeq d) (n : ℕ) (ω : ℕ → EuclideanSpace ℝ (Fin d) × ℝ) (y : ℝ) : ℝ :=
  ∑ i : Fin n, W n (ω 0).1 (fun j => (ω (j.val + 1)).1) i * (if (ω (i.val + 1)).2 ≤ y then 1 else 0)

/-- The estimated lower `p`th quantile `L̂ₙ^Y(p | X) = inf [y : F̂ₙ^Y(y | X) ≥ p]` (§7, p. 603). For
probability weights, `n ≥ 1` and `0 < p < 1`, `F̂ₙ^Y(· | X)` is a step distribution function equal to `0`
below `minᵢ Yᵢ` and to `1` from `maxᵢ Yᵢ` on, so the set is nonempty and bounded below and the real
`sInf` is the page's infimum. At `n = 0` the set is empty and the value is the junk `0`; no limit
statement sees it. -/
noncomputable def estLowerQ {d : ℕ} (W : StoneRegression.Criterion.WeightSeq d) (n : ℕ) (p : ℝ)
    (ω : ℕ → EuclideanSpace ℝ (Fin d) × ℝ) : ℝ :=
  sInf {y : ℝ | p ≤ estCdf W n ω y}

/-- The estimated upper `p`th quantile `Ûₙ^Y(p | X) = sup [y : F̂ₙ^Y(y | X) ≤ p]` (§7, p. 603). For
probability weights, `n ≥ 1` and `0 < p < 1` the set is nonempty and bounded above, so the real `sSup`
is the page's supremum. At `n = 0` the set is all of `ℝ` and the value is the junk `0`; no limit
statement sees it. -/
noncomputable def estUpperQ {d : ℕ} (W : StoneRegression.Criterion.WeightSeq d) (n : ℕ) (p : ℝ)
    (ω : ℕ → EuclideanSpace ℝ (Fin d) × ℝ) : ℝ :=
  sSup {y : ℝ | estCdf W n ω y ≤ p}

end StoneRegression.Quantile
