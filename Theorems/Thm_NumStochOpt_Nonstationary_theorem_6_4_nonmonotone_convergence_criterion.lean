import Mathlib
import Definitions.Def_NumStochOpt_Nonstationary_ExitTime

open Filter Topology

namespace NumStochOpt.Nonstationary

/-- Theorem 6.4 (Ermoliev, Ch. 6 of Ermoliev & Wets (1988), p. 155, citing [5, p. 181]): a
convergence criterion for nonmonotone sequences. Let `X* ⊆ ℝⁿ` be closed and `(x^s)` a sequence
in `ℝⁿ` such that
(1) all `x^s` lie in a compact set `K`;
(2) for every subsequence `x^{s_k} → x'`:
  (a) if `x' ∈ X*` then `‖x^{s_k+1} - x^{s_k}‖ → 0`;
  (b) if `x' ∉ X*` then for all sufficiently small `ε > 0` and every `k` the exit time
      `τ_k = min {s ≥ s_k | ‖x^s - x^{s_k}‖ > ε}` is finite, and
(3) for a continuous `V` taking at most countably many values on `X*`,
    `limsup_k V(x^{τ_k}) < lim_k V(x^{s_k}) = V(x')`.
Then `V(x^s)` converges and every accumulation point of `(x^s)` lies in `X*`.
The page prints `τ_k = min{s | s ≥ s_k, ‖x^{s_k} - x^s‖ < ε} > ∞`; the reading used is the
one the proof of Theorem 6.3 (pp. 155–156) verifies. -/
theorem theorem_6_4_nonmonotone_convergence_criterion {n : ℕ}
    (Xstar K : Set (EuclideanSpace ℝ (Fin n))) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (V : EuclideanSpace ℝ (Fin n) → ℝ)
    (hXstar : IsClosed Xstar)
    (hK : IsCompact K) (hxK : ∀ s, x s ∈ K)
    (h2a : ∀ (φ : ℕ → ℕ) (x' : EuclideanSpace ℝ (Fin n)), StrictMono φ →
      Tendsto (x ∘ φ) atTop (𝓝 x') → x' ∈ Xstar →
        Tendsto (fun k => ‖x (φ k + 1) - x (φ k)‖) atTop (𝓝 0))
    (hV : Continuous V) (hVcount : (V '' Xstar).Countable)
    (h2b3 : ∀ (φ : ℕ → ℕ) (x' : EuclideanSpace ℝ (Fin n)), StrictMono φ →
      Tendsto (x ∘ φ) atTop (𝓝 x') → x' ∉ Xstar →
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
          (∀ k, ∃ s, φ k ≤ s ∧ ε < ‖x s - x (φ k)‖) ∧
          limsup (fun k => V (x (exitTime x (φ k) ε))) atTop < V x') :
    (∃ L : ℝ, Tendsto (fun s => V (x s)) atTop (𝓝 L)) ∧
      ∀ x' : EuclideanSpace ℝ (Fin n), MapClusterPt x' atTop x → x' ∈ Xstar := by sorry

end NumStochOpt.Nonstationary

