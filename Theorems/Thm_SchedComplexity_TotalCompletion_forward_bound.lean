import Mathlib
import Definitions.Def_SchedComplexity_TotalCompletion_SingleMachine
import Definitions.Def_SchedComplexity_TotalCompletion_Construction

namespace SchedComplexity.TotalCompletion

/-- Proof of Theorem 4(a), forward direction (p. 22): if `Σ_{j∈S} a_j = b`, then the schedule of
the processing order `({J_j | j ∈ S'}, {J_j | j ∈ S}, J_n, {J_j | j ∈ T'−S'}, {J_j | j ∈ T−S},
{J_j | j ∈ U})`, with `S' = {t + j | j ∈ T−S}` and any order inside each group, is feasible and
has `Σ_{j∉U} C_j ≤ u`, `Σ_{j∈U} C_j = uσ + ½u(u + 1)υ` and `Σ_j C_j ≤ y`. -/
theorem forward_bound {t : ℕ} (a : Fin t → ℕ) (b : ℕ)
    (ha : ∀ i, 0 < a i) (hb : 0 < b) (hbA : b < sumA a)
    (S : Finset (Fin t)) (hS : ∑ i ∈ S, a i = b)
    (l₁ l₂ l₃ l₄ l₅ : List (Fin (numJobs a b)))
    (h₁ : l₁.Nodup ∧ l₁.toFinset = jobsShift a b Sᶜ)
    (h₂ : l₂.Nodup ∧ l₂.toFinset = jobsT a b S)
    (h₃ : l₃.Nodup ∧ l₃.toFinset = groupT' a b \ jobsShift a b Sᶜ)
    (h₄ : l₄.Nodup ∧ l₄.toFinset = jobsT a b Sᶜ)
    (h₅ : l₅.Nodup ∧ l₅.toFinset = groupU a b) :
    let B := orderSchedule (procTime a b) (release a b)
      (l₁ ++ l₂ ++ [lastJob a b] ++ l₃ ++ l₄ ++ l₅)
    IsFeasible (procTime a b) (release a b) B ∧
      ∑ j ∈ (groupU a b)ᶜ, completion (procTime a b) B j ≤ uCount a b ∧
      ∑ j ∈ groupU a b, completion (procTime a b) B j =
        uCount a b * sigma a b + uCount a b * (uCount a b + 1) / 2 * upsilon a b ∧
      ∑ j, completion (procTime a b) B j ≤ yThreshold a b := by sorry

end SchedComplexity.TotalCompletion

