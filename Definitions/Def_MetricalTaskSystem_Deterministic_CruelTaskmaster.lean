import Mathlib
import Definitions.Def_MetricalTaskSystem_Deterministic_Model

namespace MetricalTaskSystem.Deterministic

/-- The prefix `T¹ ⋯ Tᵐ` of an infinite task sequence `T : ℕ → S → ℝ`
(where `T i` is the paper's `T^{i+1}`). -/
def prefixSeq {S : Type} (T : ℕ → S → ℝ) (m : ℕ) : Fin m → S → ℝ :=
  fun i => T i

/-- The competitive ratio of `A` with respect to an infinite task sequence (p. 748–749):
`w_T(A) = limsup_{m → ∞} c_A(T¹ ⋯ Tᵐ) / c₀(T¹ ⋯ Tᵐ)`, computed in `EReal` (it may be `+∞`).
The quotient is the real quotient, so a prefix with `c₀ = 0` contributes the value `0`;
this does not affect the `limsup` when `c₀ → ∞`. -/
noncomputable def ratioLimsup {S : Type} [Fintype S] [DecidableEq S] (d : S → S → ℝ)
    (A : OnlineAlgorithm S) (s₀ : S) (T : ℕ → S → ℝ) : EReal :=
  Filter.limsup
    (fun m : ℕ => ((onlineCost d A s₀ (prefixSeq T m) / offlineOpt d s₀ (prefixSeq T m) : ℝ) :
      EReal))
    Filter.atTop

/-- The `ε`-elementary task with its nonzero entry at state `u`:
`T(u) = ε` and `T(s) = 0` for `s ≠ u` (p. 748). -/
def elemTask {S : Type} [DecidableEq S] (ε : ℝ) (u : S) : S → ℝ :=
  fun s => if s = u then ε else 0

/-- The states `[σ(0), σ(1), …, σ(i)]` of algorithm `A` played against the **cruel taskmaster**
`M(ε)` (p. 748): `σ(0) = s₀`, the task `T^{j}` is the `ε`-elementary task at `σ(j − 1)`, and
`σ(j) = A(s₀, [T¹, …, T^j])`. -/
def cruelStates {S : Type} [DecidableEq S] (A : OnlineAlgorithm S) (s₀ : S) (ε : ℝ) :
    ℕ → List S
  | 0 => [s₀]
  | i + 1 =>
    let l := cruelStates A s₀ ε i
    l ++ [A s₀ (l.map (elemTask ε))]

/-- The state `σ(i)` of `A` against the cruel taskmaster `M(ε)`. -/
def cruelState {S : Type} [DecidableEq S] (A : OnlineAlgorithm S) (s₀ : S) (ε : ℝ) (i : ℕ) :
    S :=
  (cruelStates A s₀ ε i).getLastD s₀

/-- The infinite task sequence `T(ε)` produced by `M(ε)` in response to `A` (p. 748–749):
its `(i+1)`-st task (index `i`) is `ε` at `σ(i)` and `0` elsewhere. -/
def cruelSeq {S : Type} [DecidableEq S] (A : OnlineAlgorithm S) (s₀ : S) (ε : ℝ) :
    ℕ → S → ℝ :=
  fun i => elemTask ε (cruelState A s₀ ε i)

/-- `min_{i ≠ j} d(i, j)`, defined when `S` has at least two states. -/
noncomputable def minOffDiag {S : Type} [Fintype S] [DecidableEq S] [Nontrivial S]
    (d : S → S → ℝ) : ℝ :=
  (Finset.univ.filter (fun p : S × S => p.1 ≠ p.2)).inf'
    (by
      obtain ⟨a, b, hab⟩ := exists_pair_ne S
      exact ⟨(a, b), by simpa using hab⟩)
    (fun p => d p.1 p.2)

end MetricalTaskSystem.Deterministic
