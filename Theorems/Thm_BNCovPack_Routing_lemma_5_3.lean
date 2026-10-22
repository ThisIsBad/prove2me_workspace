import Mathlib
import Definitions.Def_BNCovPack_Routing_Routing
import Definitions.Def_BNCovPack_Routing_Potential
import Definitions.Def_BNCovPack_Routing_Algorithm

namespace BNCovPack.Routing

/-- Lemma 5.3, Buchbinder–Naor 2009, p. 15. Let `E` be a non-empty finite set of `m` edges with
capacities `u e > 0`, and `B = exp(1 + ln(2m)/u(min)) − 1`.
1. Initially (no flow, no edge used, no request served) `Φ ≤ 1`.
2. `Φ > 0` in every state.
3. Let a request with path list `ps` have its flows raised by `g` (`g[j] ≥ 0` on the `j`-th path,
   `∑_j g[j] ≤ 1`), from any state with total flow `T`, edge loads `L`, edge usage `χ` and `s`
   served requests. Then either serving the request on some flow path (a path `ps[j]` with
   `g[j] > 0`), or rejecting it, gives a potential (computed with the raised flows) at most the
   potential before the increase. -/
theorem lemma_5_3 {E : Type*} [Fintype E] [Nonempty E] [DecidableEq E] (u : E → ℝ)
    (hu : ∀ e, 0 < u e) :
    potential u (roundingScale u) 0 (fun _ => 0) (fun _ => 0) 0 ≤ 1 ∧
    (∀ (T : ℝ) (L : E → ℝ) (χ : E → ℕ) (s : ℕ), 0 < potential u (roundingScale u) T L χ s) ∧
    ∀ (T : ℝ) (L : E → ℝ) (χ : E → ℕ) (s : ℕ) (ps : List (Finset E)) (g : List ℝ),
      g.length = ps.length → (∀ y ∈ g, 0 ≤ y) → g.sum ≤ 1 →
      (∃ Py ∈ ps.zip g, 0 < Py.2 ∧
          potential u (roundingScale u) (T + g.sum) (fun e => L e + pathLoad e ps g)
            (addPath χ Py.1) (s + 1) ≤ potential u (roundingScale u) T L χ s) ∨
      potential u (roundingScale u) (T + g.sum) (fun e => L e + pathLoad e ps g) χ s ≤
        potential u (roundingScale u) T L χ s := by sorry

end BNCovPack.Routing

