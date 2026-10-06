import Mathlib
import Definitions.Def_CongestionPoA_SymMax_Model

namespace CongestionPoA.SymMax

/-- Christodoulou and Koutsoupias, *The Price of Anarchy of Finite Congestion Games*, STOC 2005,
PDF p. 5, Theorems 7 and 8 (Sect. 3.4): for symmetric linear congestion games the pure price of
anarchy of the maximum social cost is at most `5/2`, and for every `N ≥ 3` some symmetric linear
instance with `N` players has a pure Nash equilibrium whose maximum cost is `(5N+1)/(2N+2)` times the
optimal one (positive) — so the bound `5/2` is tight in the limit `N → ∞`.

**Formalization Note.** First conjunct: every finite nonempty player type `ι`, every finite facility
type, affine latencies `f_e(k) = a_e k + b_e` with `a_e, b_e ≥ 0`, `MAX(A) ≤ (5/2)·MAX(P)` for every
Nash `A` and every feasible `P` (equivalent to `PA ≤ 5/2`, without dividing by the optimum). Second
conjunct: as in `theorem8_instance` — `P` is optimal for the maximum social cost, `MAX(P) > 0`, and
the ratio is exact for the pair `(A, P)`, i.e. `PA ≥ (5N+1)/(2N+2)` for the instance. -/
theorem symmetric_max_poa :
    (∀ (ι E : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype E] [DecidableEq E]
        (G : CongestionGame ι E) (A P : ι → Finset E),
        IsLinear G → IsSymmetric G → IsPureNash G A → IsProfile G P →
        maxCost G A ≤ 5 / 2 * maxCost G P) ∧
    (∀ (N : ℕ) [NeZero N], 3 ≤ N →
      ∃ (E : Type) (_ : Fintype E) (_ : DecidableEq E) (G : CongestionGame (Fin N) E)
        (A P : Fin N → Finset E),
        IsLinear G ∧ IsSymmetric G ∧ IsPureNash G A ∧ IsProfile G P ∧
        (∀ Q : Fin N → Finset E, IsProfile G Q → maxCost G P ≤ maxCost G Q) ∧
        0 < maxCost G P ∧
        maxCost G A = (5 * N + 1) / (2 * N + 2) * maxCost G P) := by sorry

end CongestionPoA.SymMax

