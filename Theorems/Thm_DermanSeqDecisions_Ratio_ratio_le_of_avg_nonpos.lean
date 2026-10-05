import Mathlib
import Definitions.Def_SennottDP_AvgFinite_Model
import Definitions.Def_DermanSeqDecisions_Ratio_Criteria

open SennottDP.AvgFinite

namespace DermanSeqDecisions.Ratio

/-- **"…which implies ψ_{R*(v)}(i) ≦ m_v."** (Derman, *On Sequential Decisions and Markov
Chains*, Management Science 9(1):16–24 (1962), DOI 10.1287/mnsc.9.1.16, §4, proof of Theorem 3,
p. 23).

Assume Assumption A, let `w′ > 0`, `w″ > 0` be two cost sets and `f ∈ C″` a deterministic
stationary procedure. If the long-run average expected cost of `f` for the signed cost `w_ik = w′_ik − m w″_ik`
satisfies `Q_f(i) ≤ 0`, then `ψ_f(i) ≤ m`.

**Formalization Note.** The statement is for stationary `f` only, as on the page (`R*(v) ∈ C″`);
for history-dependent procedures the implication can fail. Assumption A is a hypothesis because
the step is made inside the proof of Theorem 3, which assumes it, and the page justifies it through
the display for `ψ_R`, `R ∈ C′`, which needs it. `M.C` plays no role. -/
theorem ratio_le_of_avg_nonpos {S Act : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype Act] [DecidableEq Act] (M : MDC S Act) (hA : ∀ s, M.A s = Finset.univ)
    (hAssA : AssumptionA M)
    (w' w'' : S → Act → ℝ) (hw' : ∀ s a, 0 < w' s a) (hw'' : ∀ s a, 0 < w'' s a)
    (f : StationaryPolicy M) (i : S) (m : ℝ)
    (hQ : avgCostR f.toPolicy i (fun s a => w' s a - m * w'' s a) ≤ 0) :
    ratioCost f.toPolicy i w' w'' ≤ m := by sorry

end DermanSeqDecisions.Ratio

