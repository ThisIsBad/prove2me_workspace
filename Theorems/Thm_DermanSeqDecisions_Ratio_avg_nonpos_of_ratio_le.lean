import Mathlib
import Definitions.Def_SennottDP_AvgFinite_Model
import Definitions.Def_DermanSeqDecisions_Ratio_Criteria

open SennottDP.AvgFinite

namespace DermanSeqDecisions.Ratio

/-- **"Using rule R(v) we have Q_{R(v)}(i) ≦ 0."** (Derman, *On Sequential Decisions and Markov
Chains*, Management Science 9(1):16–24 (1962), DOI 10.1287/mnsc.9.1.16, §4, proof of Theorem 3,
p. 23).

Let `w′ > 0`, `w″ > 0` be two cost sets. If a procedure `θ` has ratio criterion
`ψ_θ(i) ≤ m`, then the long-run average expected cost of `θ` for the signed cost
`w_ik = w′_ik − m w″_ik` satisfies `Q_θ(i) ≤ 0`.

**Formalization Note.** The page has `ψ_{R(v)}(i) = m_v`; the hypothesis `ψ_θ(i) ≤ m` contains
that case. `θ` is an arbitrary history-dependent randomized procedure. `M.C` plays no role. -/
theorem avg_nonpos_of_ratio_le {S Act : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype Act] [DecidableEq Act] (M : MDC S Act) (hA : ∀ s, M.A s = Finset.univ)
    (w' w'' : S → Act → ℝ) (hw' : ∀ s a, 0 < w' s a) (hw'' : ∀ s a, 0 < w'' s a)
    (θ : Policy M) (i : S) (m : ℝ) (hψ : ratioCost θ i w' w'' ≤ m) :
    avgCostR θ i (fun s a => w' s a - m * w'' s a) ≤ 0 := by sorry

end DermanSeqDecisions.Ratio

