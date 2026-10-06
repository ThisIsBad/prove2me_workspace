import Mathlib
import Definitions.Def_OnlineRandomization_Restart_Model
import Definitions.Def_OnlineRandomization_Restart_GameProperties
import Definitions.Def_OnlineRandomization_Restart_RestartAlgorithm

namespace OnlineRandomization.Restart

/-- Theorem 4.1 (p. 17), through its construction (p. 18). Let `F` be a monotone, local game
with finite request set `R`, finite answer set `A`, `f_0 ≥ 0`, and diameter at most `D`.
Let `α(x) = d·x` with `d ≥ 1`, let `ε > 0` and `H = (2 + ε) D / ε`. Then
1. `R_H` is finite;
2. the restart algorithm consults `A_H` only on `R_H`;
3. for every `A_H` that is `α`-competitive on `R_H`, the restart algorithm built from `A_H`
   is `(1 + ε)α`-competitive. -/
theorem theorem_4_1 {R A : Type*} [Fintype R] [Nonempty R] [Fintype A] [Nonempty A]
    (F : Game R A) (hmono : IsMonotone F) (hloc : IsLocal F) (hf0 : 0 ≤ F.cost [] [])
    (D : ℝ) (hD : DiameterBound F D) (d : ℝ) (hd : 1 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    {r : List R | InRH F ((2 + ε) * D / ε) r}.Finite ∧
    (∀ AH AH' : DetAlg R A, (∀ r : List R, InRH F ((2 + ε) * D / ε) r → AH r = AH' r) →
      restart F ((2 + ε) * D / ε) AH = restart F ((2 + ε) * D / ε) AH') ∧
    (∀ AH : DetAlg R A,
      (∀ r : List R, InRH F ((2 + ε) * D / ε) r → AH.costOn F r ≤ d * F.opt r) →
      IsCompetitive F (fun x => (1 + ε) * (d * x)) (restart F ((2 + ε) * D / ε) AH)) := by sorry

end OnlineRandomization.Restart

