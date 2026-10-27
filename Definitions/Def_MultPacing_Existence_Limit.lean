import Mathlib
import Definitions.Def_MultPacing_Existence_Smoothed

namespace MultPacing.Existence

open Filter Topology

variable {N G : Type*} [Fintype N] [DecidableEq N] [Fintype G]

/-- The setting of the proof of Theorem 1 (p. 12): a sequence of smoothed versions `(ε_l, H_l)` of the
pacing game `P` with `H_l > M/ε_l`, `ε_l → 0` and `H_l → ∞`, where `M` bounds every buyer's
`∑_j v_ij + 2ε_l`; a pure-strategy Nash equilibrium `α_l` of the `l`-th smoothed game; and limits
`αs`, `xs`, `ps`, `ss` of the multipliers, allocations `x^l_ij`, prices `p^l_ij` and payments
`s^l_ij` along the sequence. -/
structure IsSmoothedLimit (P : PacingGame N G) (ε H : ℕ → ℝ) (M : ℝ) (α : ℕ → N → ℝ)
    (αs : N → ℝ) (xs ps ss : N → G → ℝ) : Prop where
  eps_pos : ∀ l, 0 < ε l
  M_bound : ∀ l i, ∑ j, P.v i j + 2 * ε l ≤ M
  H_gt : ∀ l, M / ε l < H l
  eps_tendsto : Tendsto ε atTop (𝓝 0)
  H_tendsto : Tendsto H atTop atTop
  equilibrium : ∀ l, IsSmoothedPNE P (ε l) (H l) (α l)
  alpha_tendsto : Tendsto α atTop (𝓝 αs)
  alloc_tendsto : ∀ i j, Tendsto (fun l => smAlloc P (ε l) (α l) i j) atTop (𝓝 (xs i j))
  price_tendsto : ∀ i j, Tendsto (fun l => smPrice P (ε l) (α l) i j) atTop (𝓝 (ps i j))
  pay_tendsto : ∀ i j, Tendsto (fun l => smPay P (ε l) (α l) i j) atTop (𝓝 (ss i j))

end MultPacing.Existence
