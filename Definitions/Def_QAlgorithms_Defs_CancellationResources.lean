import Definitions.Def_QAlgorithms_Defs_CancellationExperiments
noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.ProbabilisticCancellation

/-- arxiv-1612.02058v3 PDF p.3; arxiv-1612.02058v3 PDF p.4. -/
def repeatedExperiment {n m L : ℕ} {B : NoisyCircuits.ChannelBasis n m}
    {ideal : Matrix.unitaryGroup (Qubits n) ℂ} (Q : QPR B L ideal)
    (M : ℕ) (_hM : 0 < M) : List (PMF ((Fin L → Fin m) × Qubits n)) :=
  List.replicate M (trialLaw Q)

/-- arxiv-1612.02058v3 PDF p.3; arxiv-1612.02058v3 PDF p.4. -/
def precisionBudget (gamma delta : ℝ) (_hg : 1 ≤ gamma) (_hd : 0 < delta) : ℕ :=
  ⌈(gamma/delta)^2⌉₊

/-- Word-run/readout count from the actual repeated list (1612.02058 pp.3--4). -/
def experimentRunCount {n m L : ℕ} {B : NoisyCircuits.ChannelBasis n m}
    {ideal : Matrix.unitaryGroup (Qubits n) ℂ} (Q : QPR B L ideal)
    (M : ℕ) (hM : 0 < M) : ℕ := (repeatedExperiment Q M hM).length

/-- Each fresh trial executes one length-L word (1612.02058 pp.3--4). -/
def experimentOperationCount {n m L : ℕ} {B : NoisyCircuits.ChannelBasis n m}
    {ideal : Matrix.unitaryGroup (Qubits n) ℂ} (Q : QPR B L ideal)
    (M : ℕ) (hM : 0 < M) : ℕ :=
  ((repeatedExperiment Q M hM).map fun _ => L).sum

/-- Sanity check for the source model (arxiv-1612.02058v3 PDF p.3). -/
example : precisionBudget 1 1 le_rfl (by norm_num) = 1 := by norm_num [precisionBudget]

end QAlgorithms.ProbabilisticCancellation
