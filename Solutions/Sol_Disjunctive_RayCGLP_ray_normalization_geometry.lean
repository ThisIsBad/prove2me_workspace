import Mathlib
import Definitions.Def_Disjunctive_RayCGLP_Basic

open Disjunctive.RayCGLP

theorem solution : ¬ (∀ {n : ℕ} (PD : Set (Fin n → ℝ)) (hPDconv : Convex ℝ PD)
    (hPDclosed : IsClosed PD) (xbar xstar : Fin n → ℝ)
    (hxstar : xstar ∈ PD),
    ∃ alphaT betaT, IsCGLPYOptimal PD (xstar - xbar) xbar alphaT betaT ∧
      dotProduct alphaT xbar < betaT ∧ (∀ x ∈ PD, betaT ≤ dotProduct alphaT x) ∧
      ∃ t : ℝ, IsGreatest
        {t' : ℝ | t' ∈ Set.Ioc (0 : ℝ) 1 ∧
          dotProduct alphaT (xbar + t' • (xstar - xbar)) = betaT} t) := by
  intro h
  obtain ⟨α, β, ⟨⟨_, hy⟩, _⟩, _⟩ :=
    h (n := 1) Set.univ convex_univ isClosed_univ 0 0 (Set.mem_univ _)
  simp at hy

#print axioms solution
