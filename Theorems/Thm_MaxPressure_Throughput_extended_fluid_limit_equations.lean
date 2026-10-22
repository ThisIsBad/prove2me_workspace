import Mathlib
import Definitions.Def_MaxPressure_Throughput_Dynamics

namespace MaxPressure.Throughput

/-- Lemma 5, p. 214: an extended maximum-pressure fluid limit satisfies
(14)–(17), (52)–(55). The derivative clause includes its existence when
the allocation is strictly dominated. -/
theorem extended_fluid_limit_equations {I J K : ℕ} {Ω : Type*}
    (N : Network I J K) (hN : N.Standing) (hEAA : EAA N)
    (E : Finset (Fin J → ℝ)) (hE : (E : Set (Fin J → ℝ)) = extremeAllocs N)
    (P : Primitives I J Ω) (Z : Ω → ℝ → Fin I → ℝ)
    (Ta : Ω → (Fin J → ℝ) → ℝ → ℝ) (ω : Ω)
    (heq : NetworkEquations N P Z (activityTime E Ta) ω)
    (hmp : MPProcess N E Z Ta ω)
    (Zb : ℝ → Fin I → ℝ) (Tb : ℝ → Fin J → ℝ)
    (Tab : (Fin J → ℝ) → ℝ → ℝ)
    (hlim : IsMPFluidLimit N P E Z Ta ω Zb Tb Tab) :
    IsFluidSolution N Zb Tb ∧
    (∀ t, 0 ≤ t → ∀ j, Tb t j = ∑ a ∈ E, a j * Tab a t) ∧
    (∀ a ∈ E, MonotoneOn (Tab a) (Set.Ici (0 : ℝ))) ∧
    (∀ t, 0 ≤ t → ∑ a ∈ E, Tab a t = t) ∧
    (∀ t, 0 < t → ∀ a ∈ E,
      (∃ a' ∈ E, pressure N a (Zb t) < pressure N a' (Zb t)) →
      HasDerivAt (Tab a) 0 t) := by sorry

end MaxPressure.Throughput

