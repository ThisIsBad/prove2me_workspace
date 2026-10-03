import Mathlib
import Definitions.Def_SennottDP_DiscountedASM_MDC

open scoped ENNReal NNReal
open Classical

namespace SennottDP.DiscountedASM

namespace MDC

variable {S Act : Type} (M : MDC S Act)

/-- `P^{(t)}_{ij}(f)`, the `t`-step transition probability of the Markov chain induced by the
stationary policy `f` (equation (2.7), p. 23), computed by first-step decomposition:
`P^{(0)}_{ij} = 1{i = j}`, `P^{(t+1)}_{ij} = Σ_k P_{ik}(f) P^{(t)}_{kj}`. -/
noncomputable def stepProb (f : S → Act) : ℕ → S → S → ℝ≥0∞
  | 0, i, j => if i = j then 1 else 0
  | t + 1, i, j => ∑' k, M.P i (f i) k * stepProb f t k j

/-- The taboo probability `_{T*}P^{(t)}_{ij}(f)` (p. 78): the probability that the chain of the
stationary policy `f` goes from `i` to `j` in `t ≥ 1` steps while staying in the finite set `T`
at the intermediate times `1, …, t-1` (the initial and final states are unrestricted):
`_{T*}P^{(1)}_{ij} = P_{ij}(f)`, `_{T*}P^{(t+1)}_{ij} = Σ_{k ∈ T} P_{ik}(f) _{T*}P^{(t)}_{kj}`.
The value at `t = 0` (`1{i = j}`) is a convention and is not used. -/
noncomputable def tabooProb (T : Finset S) (f : S → Act) : ℕ → S → S → ℝ≥0∞
  | 0, i, j => if i = j then 1 else 0
  | 1, i, j => M.P i (f i) j
  | t + 2, i, j => ∑' k, (if k ∈ T then M.P i (f i) k * tabooProb T f (t + 1) k j else 0)

/-- `E_f[α^{T}]` for the first passage time `T ≥ 1` of the chain of `f`, started at `i`, into
the complement `S - T` of the finite set `T`, counting `α^∞ = 0` (equation (4.45), p. 79):
`Σ_{n ≥ 1} α^n P(T = n)` with `P(T = n) = Σ_{j ∉ T} _{T*}P^{(n)}_{ij}(f)`. -/
noncomputable def firstPassageDisc (T : Finset S) (f : S → Act) (α : ℝ≥0) (i : S) : ℝ≥0∞ :=
  ∑' n : ℕ, (α : ℝ≥0∞) ^ (n + 1) *
    ∑' j : S, (if j ∈ T then 0 else M.tabooProb T f (n + 1) i j)

end MDC

end SennottDP.DiscountedASM
