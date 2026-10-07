import Mathlib
import Definitions.Def_BellmanDP_Games_MultiStage

namespace BellmanDP.Games

/-- Bellman, *Dynamic Programming*, Ch. X, Theorem 4, pp. 301–302 (stability). Let the games `g`
(return `R`) and `g'` (the same data with return `R'`) both satisfy the hypotheses of Theorem 1
with the same `k`, and let `f`, `F` be the solutions of the corresponding equations (16.2) in the
class of Theorem 1. With
`Δ(c) = Max_{‖P‖ + ‖P'‖ ≤ c} Max_{u ∈ S, v ∈ S'} |R(u, v) − R'(u, v)|`,
`|f(P, P') − F(P, P')| ≤ Σ_{n=0}^∞ Δ(kⁿ c)` for `c ≥ ‖P‖ + ‖P'‖`. The maximum `Δ` is expressed
through a majorant: the bound holds for every `Δ'` dominating `|R − R'|` on the regions
`‖P‖ + ‖P'‖ ≤ c` with `Σ_n Δ'(kⁿ c)` convergent. -/
theorem stability_estimate {n n' m m' : ℕ} (g : GameData n n' m m') (R' : Vec m → Vec m' → ℝ)
    (k : ℝ) (hg : GameHyp g k) (hg' : GameHyp { g with R := R' } k)
    (f F : Vec n → Vec n' → ℝ) (hf : InSolutionClass g f) (hfs : IsGameSolution g f)
    (hF : InSolutionClass { g with R := R' } F) (hFs : IsGameSolution { g with R := R' } F)
    (Δ : ℝ → ℝ)
    (hΔ : ∀ c : ℝ, ∀ P ∈ g.D, ∀ P' ∈ g.D', l1norm P + l1norm P' ≤ c →
      ∀ u ∈ (g.S P P' : Set (Vec m)), ∀ v ∈ (g.S' P P' : Set (Vec m')), |g.R u v - R' u v| ≤ Δ c)
    (P : Vec n) (hP : P ∈ g.D) (P' : Vec n') (hP' : P' ∈ g.D') (c : ℝ)
    (hc : l1norm P + l1norm P' ≤ c) (hsum : Summable (fun j : ℕ => Δ (k ^ j * c))) :
    |f P P' - F P P'| ≤ ∑' j : ℕ, Δ (k ^ j * c) := by sorry

end BellmanDP.Games

