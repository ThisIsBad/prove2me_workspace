import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Channel

namespace RetroCorr.Separation

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Elementwise

/-- One branch of a local Kraus instrument of Alice (first memory factor), Bob's memory
untouched: `X ↦ (E ⊗ I) X (E ⊗ I)†`. -/
def aliceBranch {a b h : ℕ} (E : Matrix (Fin h) (Fin a) ℂ) :
    QAlgorithms.Superop (Fin a × Fin b) (Fin h × Fin b) :=
  QAlgorithms.conjSuperop (Matrix.kronecker E (1 : Matrix (Fin b) (Fin b) ℂ))

/-- One branch of a local Kraus instrument of Bob (second memory factor), Alice's memory
untouched: `X ↦ (I ⊗ E) X (I ⊗ E)†`. -/
def bobBranch {a b h : ℕ} (E : Matrix (Fin h) (Fin b) ℂ) :
    QAlgorithms.Superop (Fin a × Fin b) (Fin a × Fin h) :=
  QAlgorithms.conjSuperop (Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) E)

/-- One channel use: Alice's memory `Fin a` is split by her choice of bijection
`e : Fin a ≃ Fin a' × I` into a kept part `Fin a'` and the channel input `I`; the input goes
through the superoperator `Φ`, whose output `O` joins Bob's memory, which becomes `Fin b'` via
`f : Fin b' ≃ O × Fin b`. Off-diagonal blocks are kept, so entanglement with both memories is
preserved: this is `id_{A'} ⊗ Φ ⊗ id_B` up to the two relabellings. -/
def sendVia {I O : Type*} {a a' b b' : ℕ} (e : Fin a ≃ Fin a' × I) (f : Fin b' ≃ O × Fin b)
    (Φ : QAlgorithms.Superop I O) :
    QAlgorithms.Superop (Fin a × Fin b) (Fin a' × Fin b') :=
  fun X p q =>
    Φ (Matrix.of fun i i' => X (e.symm (p.1, i), (f p.2).2) (e.symm (q.1, i'), (f q.2).2))
      (f p.2).1 (f q.2).1

/-- Introduction, p. 1, and Fig. 2, p. 3: adaptive protocols of Alice and Bob that use the
channel `N` (with classical output `k ∼ μ`) exactly `n` times, assisted by unlimited local
operations and free two-way classical communication, and no prior entanglement. The protocol's
state is an operator on Alice's memory `Fin a` times Bob's memory `Fin b`; the predicate holds
of the map from that state to Bob's final `m`-qubit output.
* `finish`: Bob applies a channel `D` to his memory; Alice's memory is discarded.
* `alice` / `bob`: a party applies a complete Kraus instrument (ancillas and discarding
  included through the dimensions); its outcome `i` is announced and the rest of the protocol
  may depend on it.
* `send`: a register of Alice's memory goes through the channel; Bob receives the quantum
  output, and the classical output `k` (drawn from `μ` independently at every use) is announced
  to both parties; the rest of the protocol may depend on `k`, and the outcome is averaged
  over `k`. Nothing before the use depends on its `k`. -/
inductive Adaptive {K : Type*} [MeasurableSpace K] (μ : Measure K)
    {I O : Type*} [Fintype I] [Fintype O] (N : K → QAlgorithms.Superop I O) (m : ℕ) :
    {n a b : ℕ} → QAlgorithms.Superop (Fin a × Fin b) (QAlgorithms.Qubits m) → Prop
  | finish {a b : ℕ} (D : QAlgorithms.Superop (Fin b) (QAlgorithms.Qubits m))
      (hD : QAlgorithms.IsChannel D) :
      Adaptive μ N m (n := 0) (a := a) (b := b) (fun X => D (QAlgorithms.traceLeft X))
  | alice {n a b h r : ℕ} (E : Fin r → Matrix (Fin h) (Fin a) ℂ)
      (complete : QAlgorithms.IsKrausFamily E)
      (next : Fin r → QAlgorithms.Superop (Fin h × Fin b) (QAlgorithms.Qubits m))
      (valid : ∀ i, Adaptive μ N m (n := n) (next i)) :
      Adaptive μ N m (n := n) (fun X => ∑ i, next i (aliceBranch (b := b) (E i) X))
  | bob {n a b h r : ℕ} (E : Fin r → Matrix (Fin h) (Fin b) ℂ)
      (complete : QAlgorithms.IsKrausFamily E)
      (next : Fin r → QAlgorithms.Superop (Fin a × Fin h) (QAlgorithms.Qubits m))
      (valid : ∀ i, Adaptive μ N m (n := n) (next i)) :
      Adaptive μ N m (n := n) (fun X => ∑ i, next i (bobBranch (a := a) (E i) X))
  | send {n a a' b b' : ℕ} (e : Fin a ≃ Fin a' × I) (f : Fin b' ≃ O × Fin b)
      (next : K → QAlgorithms.Superop (Fin a' × Fin b') (QAlgorithms.Qubits m))
      (valid : ∀ k, Adaptive μ N m (n := n) (next k)) :
      Adaptive μ N m (n := n + 1)
        (fun X => ∫ k, next k (sendVia e f (N k) X) ∂μ)

/-- A two-way assisted quantum code for `m` qubits using the channel `n` times: Alice encodes
the message with a channel into her memory `Fin memory`; Bob's memory starts one-dimensional
(no prior entanglement); then an `Adaptive` protocol with exactly `n` channel uses runs. -/
structure TwoWayCode {K : Type*} [MeasurableSpace K] (μ : Measure K)
    {I O : Type*} [Fintype I] [Fintype O] (N : K → QAlgorithms.Superop I O) (n m : ℕ) where
  memory : ℕ
  encode : QAlgorithms.Superop (QAlgorithms.Qubits m) (Fin memory)
  encode_channel : QAlgorithms.IsChannel encode
  run : QAlgorithms.Superop (Fin memory × Fin 1) (QAlgorithms.Qubits m)
  valid : Adaptive μ N m (n := n) run

/-- The state Bob holds at the end of the code, for the message state `ρ`. -/
def TwoWayCode.output {K : Type*} [MeasurableSpace K] {μ : Measure K}
    {I O : Type*} [Fintype I] [Fintype O] {N : K → QAlgorithms.Superop I O} {n m : ℕ}
    (P : TwoWayCode μ N n m) (ρ : Matrix (QAlgorithms.Qubits m) (QAlgorithms.Qubits m) ℂ) :
    Matrix (QAlgorithms.Qubits m) (QAlgorithms.Qubits m) ℂ :=
  P.run (Matrix.kronecker (P.encode ρ) (1 : Matrix (Fin 1) (Fin 1) ℂ))

/-- `R ≥ 0` qubits per channel use are achievable with two-way classical communication: for
every `η > 0` and every sufficiently large number `n` of channel uses there is a code for
`m ≥ R n` qubits whose fidelity `⟨ψ|output(|ψ⟩⟨ψ|)|ψ⟩` is at least `1 − η` for every pure
message state `ψ`. -/
def TwoWayAchievable {K : Type*} [MeasurableSpace K] (μ : Measure K)
    {I O : Type*} [Fintype I] [Fintype O] (N : K → QAlgorithms.Superop I O) (R : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∃ m : ℕ, R * n ≤ m ∧
    ∃ P : TwoWayCode μ N n m, ∀ ψ : EuclideanSpace ℂ (QAlgorithms.Qubits m),
      QAlgorithms.IsState ψ →
        1 - η ≤ QAlgorithms.effectProb (QAlgorithms.pureDensity ψ)
          (P.output (QAlgorithms.pureDensity ψ))

/-- Introduction, p. 1: the quantum capacity `Q₂` assisted by two-way classical communication,
in qubits per channel use: the supremum of the achievable rates, in `[0, ∞]`. -/
def twoWayQuantumCapacity {K : Type*} [MeasurableSpace K] (μ : Measure K)
    {I O : Type*} [Fintype I] [Fintype O] (N : K → QAlgorithms.Superop I O) : ENNReal :=
  sSup {q | ∃ R : ℝ, 0 ≤ R ∧ TwoWayAchievable μ N R ∧ q = ENNReal.ofReal R}

end

end RetroCorr.Separation
