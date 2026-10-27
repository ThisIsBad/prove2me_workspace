import Mathlib

namespace ThresholdMNL.Pricing

open Finset

/-- Nominal utility `u_i = α_i − β p_i` of product `i` at prices `p` (p. 12). Products are `Fin N`;
the paper's product `k` is the index `k − 1`. -/
def nomUtil {N : ℕ} (α : Fin N → ℝ) (β : ℝ) (p : Fin N → ℝ) (i : Fin N) : ℝ :=
  α i - β * p i

/-- Product `i` belongs to the threshold consideration set `Ψ(S⁺, p; Δ)` of eq. (1), `S⁺ = S ∪ {0}`:
`i ∈ S` and `u_i ≥ u_j − Δ` for every `j ∈ S⁺`, where `u0` is the nominal utility of the outside
option `0`. This is `u_i ≥ max_{j ∈ S⁺} u_j − Δ` written without a maximum. -/
def InCons {N : ℕ} (S : Finset (Fin N)) (α : Fin N → ℝ) (β u0 Δ : ℝ) (p : Fin N → ℝ)
    (i : Fin N) : Prop :=
  i ∈ S ∧ u0 - Δ ≤ nomUtil α β p i ∧ ∀ j ∈ S, nomUtil α β p j - Δ ≤ nomUtil α β p i

/-- The outside option `0` belongs to `Ψ(S⁺, p; Δ)`: `u_0 ≥ u_j − Δ` for every `j ∈ S⁺`. -/
def OutsideInCons {N : ℕ} (S : Finset (Fin N)) (α : Fin N → ℝ) (β u0 Δ : ℝ)
    (p : Fin N → ℝ) : Prop :=
  ∀ j ∈ S, nomUtil α β p j - Δ ≤ u0

open Classical in
/-- The products of the consideration set `Ψ(S⁺, p; Δ)`. -/
noncomputable def consSet {N : ℕ} (S : Finset (Fin N)) (α : Fin N → ℝ) (β u0 Δ : ℝ)
    (p : Fin N → ℝ) : Finset (Fin N) :=
  S.filter (fun i => InCons S α β u0 Δ p i)

open Classical in
/-- The denominator `∑_{j ∈ Ψ(S⁺, p; Δ)} exp(u_j)` of eq. (2) with `µ = 1`; the outside option
contributes `exp(u_0)` exactly when it is in the consideration set. -/
noncomputable def consDenom {N : ℕ} (S : Finset (Fin N)) (α : Fin N → ℝ) (β u0 Δ : ℝ)
    (p : Fin N → ℝ) : ℝ :=
  (if OutsideInCons S α β u0 Δ p then Real.exp u0 else 0) +
    ∑ j ∈ consSet S α β u0 Δ p, Real.exp (nomUtil α β p j)

open Classical in
/-- The TMNL choice probability `q_i(S, p; Δ)` of eq. (2) with `µ = 1`: `exp(u_i)` over the
denominator if `i ∈ Ψ(S⁺, p; Δ)`, and `0` otherwise. -/
noncomputable def choiceProb {N : ℕ} (S : Finset (Fin N)) (α : Fin N → ℝ) (β u0 Δ : ℝ)
    (p : Fin N → ℝ) (i : Fin N) : ℝ :=
  if InCons S α β u0 Δ p i then Real.exp (nomUtil α β p i) / consDenom S α β u0 Δ p else 0

/-- The total expected profit `R(S, p; Δ) = ∑_{i ∈ Ψ(S⁺, p; Δ)} (p_i − c_i) q_i(S, p; Δ)` of
eq. (3); the outside option earns `p_0 − c_0 = 0`. -/
noncomputable def profit {N : ℕ} (S : Finset (Fin N)) (α c : Fin N → ℝ) (β u0 Δ : ℝ)
    (p : Fin N → ℝ) : ℝ :=
  ∑ i ∈ consSet S α β u0 Δ p, (p i - c i) * choiceProb S α β u0 Δ p i

/-- The utility-net-cost ordered assortment `S_n = {1, …, n}` of Definition 1, 0-based: the indices
`i` with `i.val < n`. -/
def ordAssort (N n : ℕ) : Finset (Fin N) :=
  univ.filter (fun i : Fin N => i.val < n)

/-- The quasi-same-markup/same-utility policy of Definition 2 on `S_n`, 0-based: `1 ≤ n' ≤ n ≤ N`;
the paper's products `2, …, n'` (indices `1, …, n' − 1`) have equal markups `p_i − c_i`, and its
products `n' + 1, …, n` (indices `n', …, n − 1`) have equal nominal utilities. Product `1`
(index `0`) is unconstrained. -/
def IsQuasiSameMarkupSameUtility {N : ℕ} (α c : Fin N → ℝ) (β : ℝ) (n n' : ℕ)
    (p : Fin N → ℝ) : Prop :=
  1 ≤ n' ∧ n' ≤ n ∧ n ≤ N ∧
  (∀ i j : Fin N, 1 ≤ i.val → i.val < n' → 1 ≤ j.val → j.val < n' →
      p i - c i = p j - c j) ∧
  (∀ i j : Fin N, n' ≤ i.val → i.val < n → n' ≤ j.val → j.val < n →
      nomUtil α β p i = nomUtil α β p j)

/-- The total expected profit when the consideration set is exactly `S` (outside option excluded),
`∑_{i ∈ S} m_i exp(u_i) / ∑_{i ∈ S} exp(u_i)` with `m_i = p_i − c_i`: the formula
`R(S, m; Δ)` of the proof of Theorem 2 (OS p. 2). -/
noncomputable def exclProfit {N : ℕ} (S : Finset (Fin N)) (α c : Fin N → ℝ) (β : ℝ)
    (p : Fin N → ℝ) : ℝ :=
  (∑ i ∈ S, (p i - c i) * Real.exp (nomUtil α β p i)) / ∑ i ∈ S, Real.exp (nomUtil α β p i)

end ThresholdMNL.Pricing
