import Mathlib

namespace ExactSDPDuality.ELSD

open Matrix

/-- The inner product `A • B = ∑_{i,j} A_{ij} B_{ij}` on the space `ℳₙ` of real `n × n` matrices
(Ramana 1997, §1.3, p. 132). It is defined on all of `ℳₙ`, not only on symmetric matrices. -/
def frob {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * B i j

/-- `Q̂(x) = ∑_{i=1}^m x_i Q_i` (§1.5.1, p. 136). -/
def Qhat {n m : ℕ} (Q : Fin m → Matrix (Fin n) (Fin n) ℝ) (x : Fin m → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  ∑ i, x i • Q i

/-- The affine matrix map `Q(x) = Q₀ − Q̂(x)` (§1.5.1, p. 136). -/
def Qaff {n m : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ) (Q : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (x : Fin m → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Q0 - Qhat Q x

/-- The feasible region `G = {x | ∑ᵢ xᵢ Qᵢ ⪯ Q₀} = {x | Q(x) ⪰ 0}` of the primal SDP (P)
(§1.5.1, p. 136). Over `ℝ`, `PosSemidef` includes symmetry. -/
def feasibleSet {n m : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin m → Matrix (Fin n) (Fin n) ℝ) : Set (Fin m → ℝ) :=
  {x | (Qaff Q0 Q x).PosSemidef}

/-- `Q* : ℳₙ → ℝᵐ`, `Q*(U) = (U • Qᵢ)_{i=1,…,m}` (§1.5.1, p. 136), defined on all of `ℳₙ`. -/
def Qstar {n m : ℕ} (Q : Fin m → Matrix (Fin n) (Fin n) ℝ) (U : Matrix (Fin n) (Fin n) ℝ) :
    Fin m → ℝ :=
  fun i => frob U (Q i)

/-- `Q#(X) = 0`, where `Q#(X) = (Q₀ • X, Q*(X)) ∈ ℝᵐ⁺¹` (§1.5.1, p. 136): the conjunction
`Q₀ • X = 0` and `Q*(X) = 0`. -/
def QsharpZero {n m : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin m → Matrix (Fin n) (Fin n) ℝ) (X : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  frob Q0 X = 0 ∧ Qstar Q X = 0

/-- Membership of `(Uᵢ, Wᵢ)_{i=1}^k` in `𝒞ₖ` (p. 137):
`Q#(Uᵢ + Wᵢ₋₁) = 0` and `Uᵢ ⪰ Wᵢ Wᵢᵀ` for `i = 1, …, k`, with `W₀ = 0`.
The tuple is encoded by two sequences `U W : ℕ → ℳₙ`; only the entries `1, …, k` (and `W₀`)
matter, and the convention `U₀ = 0` is imposed so that `𝒰₀ = 𝒲₀ = {0}`.
The matrices `Wᵢ` are arbitrary (not necessarily symmetric) real matrices. -/
def IsCSeq {n m : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ) (Q : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (k : ℕ) (U W : ℕ → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  U 0 = 0 ∧ W 0 = 0 ∧
    ∀ i, 1 ≤ i → i ≤ k →
      QsharpZero Q0 Q (U i + W (i - 1)) ∧ (U i - W i * (W i)ᵀ).PosSemidef

/-- `𝒰ₖ = {Uₖ | (Uᵢ, Wᵢ)_{i=1}^k ∈ 𝒞ₖ}` (p. 137); `𝒰₀ = {0}` by convention. -/
def Uset {n m : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ) (Q : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (k : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {X | ∃ U W : ℕ → Matrix (Fin n) (Fin n) ℝ, IsCSeq Q0 Q k U W ∧ U k = X}

/-- `𝒲ₖ = {Wₖ | (Uᵢ, Wᵢ)_{i=1}^k ∈ 𝒞ₖ}` (p. 137); `𝒲₀ = {0}` by convention. -/
def Wset {n m : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ) (Q : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (k : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {X | ∃ U W : ℕ → Matrix (Fin n) (Fin n) ℝ, IsCSeq Q0 Q k U W ∧ W k = X}

/-- A pair `(U, W)` is dual feasible for (ELSD) (compact form, p. 137):
`Q*(U + W) = c`, `W ∈ 𝒲ₘ`, `U ⪰ 0`. -/
def ELSDFeasible {n m : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin m → Matrix (Fin n) (Fin n) ℝ) (c : Fin m → ℝ)
    (U W : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Qstar Q (U + W) = c ∧ W ∈ Wset Q0 Q m ∧ U.PosSemidef

/-- A pair `(U, W)` is weakly dual feasible, i.e. feasible for (Weak-ELSD) (p. 138):
`Q*(U + W) = c`, `W ∈ 𝒲ₘ₋₁`, `U ⪰ 0`. (For `m = 0`, `m - 1 = 0` and `𝒲₀ = {0}`.) -/
def WeakELSDFeasible {n m : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin m → Matrix (Fin n) (Fin n) ℝ) (c : Fin m → ℝ)
    (U W : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Qstar Q (U + W) = c ∧ W ∈ Wset Q0 Q (m - 1) ∧ U.PosSemidef

/-- The set of objective values `cᵀx` of the primal (P) over its feasible region `G`. -/
def primalValues {n m : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin m → Matrix (Fin n) (Fin n) ℝ) (c : Fin m → ℝ) : Set ℝ :=
  (fun x => c ⬝ᵥ x) '' feasibleSet Q0 Q

/-- The set of objective values `(U + W) • Q₀` of (ELSD) over its dual feasible pairs. -/
def elsdValues {n m : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin m → Matrix (Fin n) (Fin n) ℝ) (c : Fin m → ℝ) : Set ℝ :=
  {v | ∃ U W, ELSDFeasible Q0 Q c U W ∧ frob (U + W) Q0 = v}

/-- The set of objective values `(U + W) • Q₀` of (Weak-ELSD) over its weakly dual feasible
pairs. -/
def weakElsdValues {n m : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin m → Matrix (Fin n) (Fin n) ℝ) (c : Fin m → ℝ) : Set ℝ :=
  {v | ∃ U W, WeakELSDFeasible Q0 Q c U W ∧ frob (U + W) Q0 = v}

/-- The (one-sided) polar `G° = {y | xᵀy ≤ 1 ∀ x ∈ G}` of a set `G ⊆ ℝᵐ` (p. 143). -/
def polar {m : ℕ} (G : Set (Fin m → ℝ)) : Set (Fin m → ℝ) :=
  {y | ∀ x ∈ G, x ⬝ᵥ y ≤ 1}

/-- The algebraic polar `G* = {Q*(U) | U • Q₀ ≤ 1, U ⪰ 0}` (p. 143), a function of the data
`(Q₀, Q₁, …, Qₘ)` (not of the set `G`). -/
def algPolar {n m : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin m → Matrix (Fin n) (Fin n) ℝ) : Set (Fin m → ℝ) :=
  {y | ∃ U : Matrix (Fin n) (Fin n) ℝ, U.PosSemidef ∧ frob U Q0 ≤ 1 ∧ Qstar Q U = y}

/-- `Sₖ = Q*(𝒲ₖ) ⊆ ℝᵐ` (p. 145); `S₀ = Q*(𝒲₀) = {0}`. -/
def Sset {n m : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ) (Q : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (k : ℕ) : Set (Fin m → ℝ) :=
  Qstar Q '' Wset Q0 Q k

/-- The orthogonal complement `T^⊥ = {y | yᵀx = 0 ∀ x ∈ T}` of a set `T ⊆ ℝᵐ` with respect
to the dot product. -/
def perp {m : ℕ} (T : Set (Fin m → ℝ)) : Set (Fin m → ℝ) :=
  {y | ∀ x ∈ T, y ⬝ᵥ x = 0}

end ExactSDPDuality.ELSD
