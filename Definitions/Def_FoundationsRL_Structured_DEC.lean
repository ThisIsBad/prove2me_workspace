import Mathlib

namespace FoundationsRL.Structured

/-- The value of the min-max game defining the Decision-Estimation Coefficient at a reference
model `fhat` (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision
Making*, arXiv:2312.16730v1, Eq. (4.15), p. 65):

`decγ(F, f̂) := min_{p ∈ Δ(S)} max_{f ∈ F} E_{π∼p}[f(π_f) − f(π) − γ(f(π) − f̂(π))²]`.

`Π` is the (finite) decision space, `F` the function class, and `piStar f` denotes `π_f`, a
maximizer of `f` over `Π` (the book's `arg max`; callers supply that `piStar` is indeed
maximizing on every `f ∈ F` where that fact is needed). The min is realized as `sInf` over the
image, under `p`, of the `sSup` over `f ∈ F` of the payoff — a literal transcription of
`min_p max_f`, not an unconstrained bound. -/
noncomputable def decGf {S : Type*} [Fintype S] (F : Set (S → ℝ)) (piStar : (S → ℝ) → S)
    (γ : ℝ) (fhat : S → ℝ) : ℝ :=
  sInf ((fun p : S → ℝ =>
      sSup ((fun f : S → ℝ =>
          ∑ π, p π * (f (piStar f) - f π - γ * (f π - fhat π) ^ 2)) '' F))
    '' {p : S → ℝ | (∀ π, 0 ≤ p π) ∧ ∑ π, p π = 1})

/-- The Decision-Estimation Coefficient of the class `F` at scale `γ` (Eq. (4.16), p. 65):

`decγ(F) := sup_{f̂ ∈ co(F)} decγ(F, f̂)`. -/
noncomputable def dec {S : Type*} [Fintype S] (F : Set (S → ℝ)) (piStar : (S → ℝ) → S)
    (γ : ℝ) : ℝ :=
  sSup ((decGf F piStar γ) '' convexHull ℝ F)

end FoundationsRL.Structured
