import Mathlib
import Definitions.Def_StochasticProg_Recourse_Instance
import Definitions.Def_StochasticProg_LShaped_Bases
import Definitions.Def_StochasticProg_LShaped_Algorithm

namespace StochasticProg.LShaped

open StochasticProg.Recourse

variable {n1 n2 m1 m2 K : ℕ}

/-- Chapter 5, Theorem 1 (p. 194): "Assume that `W` is such that `t ∈ pos W` for all
`t ≥ 0`. Define `a_i = min_{k=1,...,K}{h_ik}` to be the componentwise minimum of `h`. Also
assume there exists one realization `hℓ, ℓ ∈ {1,...,K}` s.t. `a = hℓ`. Then, `x ∈ K2` if
and only if `Wy = a − Tx, y ≥ 0` is feasible." (`T` deterministic, as assumed on p. 193
just before the statement.)

v2 (2026-10-05): the published statement was disproved by a zero-probability realization (with `p_ℓ = 0`, `K2` ignores scenario ℓ since `0 * ⊤ = 0`). This version requires every realization to have positive probability (`hp_pos`), as §5.1 assumes (k indexes the possible realizations). -/
theorem thm1_feasibility_via_componentwise_min_v2
    (inst : Instance n1 n2 m1 m2 K) (hK : 0 < K) (hp_pos : ∀ k, 0 < inst.p k)
    (T0 : Matrix (Fin m2) (Fin n1) ℝ) (hT : ∀ k, inst.T k = T0)
    (hWpos : ∀ t : Fin m2 → ℝ, (∀ i, 0 ≤ t i) → posW inst t)
    (a : Fin m2 → ℝ) (ha : ∀ i, a i = sInf {v : ℝ | ∃ k : Fin K, v = inst.h k i})
    (ℓ : Fin K) (haℓ : a = inst.h ℓ) (x : Fin n1 → ℝ) :
    x ∈ K2 inst ↔
      ∃ y : Fin n2 → ℝ, (∀ i, 0 ≤ y i) ∧ Matrix.mulVec inst.W y = a - Matrix.mulVec T0 x := by
  sorry

end StochasticProg.LShaped

