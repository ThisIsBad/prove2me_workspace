import Mathlib
import Definitions.Def_TeschlODE_Shared_tentMap

namespace TeschlODE.Shared

/-- Teschl, §11.4, pp. 298–299, (11.16)–(11.18): the set `Λ` of points whose forward orbit under
the tent map `T_µ` stays in `[0, 1]` for all iterations, `Λ = {x ∈ ℝ | T_µⁿ(x) ∈ [0, 1] ∀ n ≥ 0}`.
For `µ > 2` this is the book's `Λ = ⋂ₙ Λₙ` (11.18), `Λₙ` being the points that stay in `[0, 1]`
for `n` iterations; for `µ = 2` it is `[0, 1]` (p. 310). -/
def tentRepellor (μ : ℝ) : Set ℝ :=
  {x | ∀ n : ℕ, (tentMap μ)^[n] x ∈ Set.Icc (0 : ℝ) 1}

end TeschlODE.Shared
