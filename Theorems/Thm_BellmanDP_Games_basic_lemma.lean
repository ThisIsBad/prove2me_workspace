import Mathlib
import Definitions.Def_BellmanDP_Games_MultiStage

namespace BellmanDP.Games

/-- Bellman, *Dynamic Programming*, Ch. X, Lemma 1, p. 294 (the basic lemma). Fix a state
`(P, P')`. Let `L = L(f)` be the value of the one-stage game with kernel
`R(u, v) + h(P, P'; u, v) f(T, T')` and `L₁ = L₁(F)` the value of the game with kernel
`R₁(u, v) + h(P, P'; u, v) F(T, T')`, both played with mixed strategies on the choice domains
`S = S(P, P')`, `S' = S'(P, P')`; that each game has a value (max-min = min-max) is a
hypothesis, as in the book's footnote 4. Then
`|L(f) − L₁(F)| ≤ Max_{u ∈ S} Max_{v ∈ S'} [|R(u, v) − R₁(u, v)| + |h(P, P'; u, v)| |f(T, T') − F(T, T')|]`,
stated as `|L − L₁| ≤ M` for every upper bound `M` of the bracket on `S × S'`. The two kernels
are assumed measurable and bounded on `S × S'`, so that the integrals exist. -/
theorem basic_lemma {n n' m m' : ℕ} (g : GameData n n' m m') (R₁ : Vec m → Vec m' → ℝ)
    (f F : Vec n → Vec n' → ℝ) (P : Vec n) (P' : Vec n') (L L₁ : ℝ)
    (hmeas : Measurable (fun z : Vec m × Vec m' => stageKernel g f P P' z.1 z.2))
    (hmeas₁ : Measurable (fun z : Vec m × Vec m' => stageKernel { g with R := R₁ } F P P' z.1 z.2))
    (hbdd : ∃ C : ℝ, ∀ u ∈ (g.S P P' : Set (Vec m)), ∀ v ∈ (g.S' P P' : Set (Vec m')),
      |stageKernel g f P P' u v| ≤ C)
    (hbdd₁ : ∃ C : ℝ, ∀ u ∈ (g.S P P' : Set (Vec m)), ∀ v ∈ (g.S' P P' : Set (Vec m')),
      |stageKernel { g with R := R₁ } F P P' u v| ≤ C)
    (hL : ValueAt g (stageKernel g f P P') P P' L)
    (hL₁ : ValueAt g (stageKernel { g with R := R₁ } F P P') P P' L₁)
    (M : ℝ)
    (hM : ∀ u ∈ (g.S P P' : Set (Vec m)), ∀ v ∈ (g.S' P P' : Set (Vec m')),
      |g.R u v - R₁ u v| + |g.h P P' u v| *
        |f (g.T P P' u v) (g.T' P P' u v) - F (g.T P P' u v) (g.T' P P' u v)| ≤ M) :
    |L - L₁| ≤ M := by sorry

end BellmanDP.Games

