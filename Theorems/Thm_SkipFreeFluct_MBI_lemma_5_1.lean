import Mathlib
import Definitions.Def_SkipFreeFluct_MBI_Chain
import Definitions.Def_SkipFreeFluct_MBI_Model
open scoped ENNReal Topology
open Filter MeasureTheory

namespace SkipFreeFluct.MBI

/-- Lemma 5.1, pp. 12–13. For an MBI with parameters `(α, µ, p, β, ν, q)`, the sequences `∆W`,
`W`, `κ`, `π` are nonnegative, and their generating functions and that of `ϖ` are, for
`s ∈ [0, s₀)`:
`∆W*[s] = (1 - s)/ψ(s)`, `W*[s] = 1/ψ(s)`, `κ*[s] = φ(s)/ψ(s)`,
`π*[s] = exp(∫_0^s φ(u)/ψ(u) du)`, `ϖ*[s] = exp(-∫_0^s φ(u)/ψ(u) du)`. -/
theorem lemma_5_1 (P : MBIParams) (hP : P.Valid) :
    (∀ k : ℕ, 0 ≤ dW P k ∧ 0 ≤ W P k ∧ 0 ≤ kappa P k ∧ 0 ≤ piSeq P k) ∧
    ∀ s ∈ Set.Ico 0 (s0 P),
      HasSum (fun k : ℕ => dW P k * s ^ k) ((1 - s) / psi P s) ∧
      HasSum (fun k : ℕ => W P k * s ^ k) (1 / psi P s) ∧
      HasSum (fun k : ℕ => kappa P k * s ^ k) (phiImm P s / psi P s) ∧
      HasSum (fun k : ℕ => piSeq P k * s ^ k)
        (Real.exp (∫ u in (0 : ℝ)..s, phiImm P u / psi P u)) ∧
      HasSum (fun k : ℕ => varpi P k * s ^ k)
        (Real.exp (-∫ u in (0 : ℝ)..s, phiImm P u / psi P u)) := by sorry

end SkipFreeFluct.MBI

