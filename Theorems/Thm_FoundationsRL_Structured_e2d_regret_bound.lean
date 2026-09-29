import Mathlib
import Definitions.Def_FoundationsRL_Structured_DEC
import Definitions.Def_FoundationsRL_Structured_OracleGuarantee
import Definitions.Def_FoundationsRL_Structured_regret

namespace FoundationsRL.Structured

/-- Proposition 13 (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive
Decision Making*, arXiv:2312.16730v1, p. 65, attributed "Foster et al. [40]"): the
Estimation-to-Decisions (E2D) algorithm's regret bound. Given a finite decision space `Π`, a
function class `F` containing the ground-truth reward function `fstar` (Assumption 5), and a
maximizer selector `piStar` (`piStar f` is `π_f`, an arg max of `f` on `Π`, for every `f ∈ F`),
suppose at each round `t` the online regression oracle produces `fhat t` and E2D selects `p t`
to (at least) attain the value of the min-max game defining `decγ(F, f̂_t)` — i.e. `p t`
certifies `decγ(F, f̂_t)` from above, as the E2D algorithm's minimizing choice does. If the
oracle's cumulative estimation error is bounded by `EstSq` (`OracleGuarantee`), then the regret
of the realized run is at most `decγ(F) · T + γ · EstSq(F, T, δ)` (Eq. (4.17)).

The book's own proof (p. 65-66) bounds regret by `sup_{f̂ : Π → ℝ} decγ(F, f̂) · T + γ ·
EstSq`, an unconstrained sup, and only equates this with `decγ(F) · T` (`decγ(F)` officially
`sup_{f̂∈co(F)} decγ(F,f̂)` by Eq. (4.16)) via Proposition 24 — a fact stated on p. 80, outside
this chunk's page range, whose own proof is left to Exercise 10 and is not otherwise given in
the chapter. Rather than invoke that unproven-in-range reduction, this formalization adds the
hypothesis that each round's oracle estimate `f̂_t` already lies in `co(F)`, matching how the
book itself describes E2D's oracle ("online estimation algorithms such as exponential weights
will produce improper predictions with f̂ ∈ co(F)", p. 65) — so the conclusion's `decγ(F)` (Eq.
4.16, over `co(F)`) directly dominates each round's `decγ(F, f̂_t)` without appeal to Prop. 24. -/
theorem e2d_regret_bound {S : Type*} [Fintype S] (F : Set (S → ℝ))
    (piStar : (S → ℝ) → S) (hpiStar : ∀ f ∈ F, ∀ π, f π ≤ f (piStar f))
    (fstar : S → ℝ) (hfstar : fstar ∈ F)
    (T : ℕ) (γ : ℝ) (hγ : 0 < γ)
    (fhat : Fin T → S → ℝ) (hfhat : ∀ t, fhat t ∈ convexHull ℝ F)
    (p : Fin T → S → ℝ)
    (hp_nonneg : ∀ t π, 0 ≤ p t π) (hp_sum : ∀ t, ∑ π, p t π = 1)
    (hp_min : ∀ t, ∀ f ∈ F,
      ∑ π, p t π * (f (piStar f) - f π - γ * (f π - fhat t π) ^ 2) ≤ decGf F piStar γ (fhat t))
    (EstSq : ℝ) (hOracle : OracleGuarantee T fhat fstar p EstSq) :
    regret fstar (piStar fstar) T p ≤ dec F piStar γ * T + γ * EstSq := by sorry

end FoundationsRL.Structured
