import Mathlib
import Definitions.Def_OnlineRandomization_Potential_Behavioural

namespace OnlineRandomization.Potential

open MeasureTheory

/-- Manuscript p. 14, Definition 3.1: `Φ` is an augmented potential function for `α` and the
behavioural randomized algorithm `g`. `Φ r a b` is `Φ_n(r, a, b)` on lists of common length `n`
(requests, algorithm's answers, adversary's answers); other values are never used.
1. `Φ_0 = 0`;
2. `Φ_n(r, a, b) ≤ α(f_n(r, b)) − f_n(r, a)` for every configuration;
3. for every configuration, every `r_{n+1} = x ∈ R` and `b_{n+1} = b' ∈ A`,
   `E[Φ_{n+1}(r x, a a_{n+1}, b b')] ≥ Φ_n(r, a, b)` with `a_{n+1} ∼ g_{n+1}(r x, a)`. -/
structure IsAugPotential {R A : Type*} [Fintype A] (F : Game R A) (α : ℝ → ℝ)
    (g : BehAlg R A) (Φ : List R → List A → List A → ℝ) : Prop where
  zero : Φ [] [] [] = 0
  le_residue : ∀ (r : List R) (a b : List A), a.length = r.length → b.length = r.length →
    Φ r a b ≤ α (F.cost r b) - F.cost r a
  le_step : ∀ (r : List R) (a b : List A), a.length = r.length → b.length = r.length →
    ∀ (x : R) (b' : A),
      Φ r a b ≤ ∑ a' : A, (g (r ++ [x]) a a').toReal * Φ (r ++ [x]) (a ++ [a']) (b ++ [b'])

/-- Manuscript p. 15, Theorem 3.1: the deterministic algorithm `M = (m_n)` obeys the potential
rule for `Φ` and the randomized algorithm `H` (coins `y`) if, for every `r ∈ R^n` and every
`r' = r x`, its answer `m_{n+1}(r') = M (r ++ [x])` satisfies
`E_y[Φ_{n+1}(r', M(r) m_{n+1}(r'), H_y(r'))] ≥ E_y[Φ_n(r, M(r), H_y(r))]`. -/
def ObeysPotentialRule {R A Ω : Type*} [MeasurableSpace Ω]
    (Φ : List R → List A → List A → ℝ) (H : RandAlg R A Ω) (M : DetAlg R A) : Prop :=
  ∀ (r : List R) (x : R),
    (∫ y, Φ r (M.answers r) ((H.alg y).answers r) ∂H.μ) ≤
      ∫ y, Φ (r ++ [x]) (M.answers r ++ [M (r ++ [x])]) ((H.alg y).answers (r ++ [x])) ∂H.μ

end OnlineRandomization.Potential
