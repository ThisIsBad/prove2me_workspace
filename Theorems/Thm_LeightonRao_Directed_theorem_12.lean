import Mathlib
import Definitions.Def_LeightonRao_Directed_Setting

namespace LeightonRao.Directed

/-- Leighton–Rao, Theorem 12, p. 804. There is an absolute constant `c > 0` such that for every
directed UMFP with `n ≥ 2` nodes, `c · 𝒮 / log₂ n ≤ f ≤ 𝒮`, where `f` is the max-flow and `𝒮` the
directed min-cut. -/
theorem theorem_12 :
    ∃ c : ℝ, 0 < c ∧ ∀ {V : Type} [Fintype V] [DecidableEq V] (N : DiNetwork V),
      2 ≤ Fintype.card V →
      c * diMinCut N / Real.logb 2 (Fintype.card V) ≤ diMaxFlow N diDemand ∧
      diMaxFlow N diDemand ≤ diMinCut N := by sorry

end LeightonRao.Directed

