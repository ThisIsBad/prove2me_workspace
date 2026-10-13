import Mathlib
import Definitions.Def_StochApproxDyn_MartingaleNoise_Interpolation

namespace StochApproxDyn.MartingaleNoise

open MeasureTheory

/-- A Robbins–Monro algorithm (Benaïm 1999, §4.1 p. 11 and §4.2 p. 14).

On a probability space `(Ω, ℱ, P)` with a nondecreasing sequence `ℱ_n` of sub-σ-algebras, the
random sequence `x` is given by scheme (7), `x_{n+1} - x_n = γ_{n+1} (F(x_n) + U_{n+1})`, with
the standing assumptions of §4.1 (`F : ℝ^d → ℝ^d` continuous, `γ` a step sequence), and
satisfies the Robbins–Monro (martingale difference noise) condition:
(i) `γ` is deterministic (it is a fixed real sequence, not a random one);
(ii) `U_n` is `ℱ_n`-measurable;
(iii) `E(U_{n+1} | ℱ_n) = 0`, where `U_{n+1}` is integrable so that the conditional expectation
is the genuine one. The paper indexes `U` from `1`; `U 0` is not used. -/
def IsRobbinsMonro {d : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω)
    (ℱ : Filtration ℕ m0) (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (γ : ℕ → ℝ) (x U : ℕ → Ω → EuclideanSpace ℝ (Fin d)) : Prop :=
  Continuous F ∧ IsStepSequence γ ∧
  (∀ n ω, x (n + 1) ω - x n ω = γ (n + 1) • (F (x n ω) + U (n + 1) ω)) ∧
  (∀ n : ℕ, StronglyMeasurable[ℱ (n + 1)] (U (n + 1))) ∧
  (∀ n : ℕ, Integrable (U (n + 1)) P) ∧
  (∀ n : ℕ, P[U (n + 1) | ℱ n] =ᵐ[P] 0)

end StochApproxDyn.MartingaleNoise
