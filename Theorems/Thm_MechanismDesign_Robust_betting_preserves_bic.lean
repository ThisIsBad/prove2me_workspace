import Mathlib
import Definitions.Def_MechanismDesign_Robust_Mechanisms

open scoped ENNReal

namespace MechanismDesign.Robust

/-- Proposition 10.7 (Börgers pp.186–187), betting, with the signs of the transfers in (v)
corrected (see below). Let `N ≥ 3`, `i ≠ j`, `p, ε ∈ (0, 1)`, `T̂_i ⊆ T_i`, `T̂_j ⊆ T_j` and
`T̂_{-i,j} ⊊ T_{-i,j}` be such that
(i) every type of `i` gives `T̂_j` positive probability and every type of `j` gives `T̂_i`
positive probability;
(ii) `β̂_i(τ_i)[T̂_{-i,j} | T̂_j] ≤ p − ε` for `τ_i ∈ T̂_i` and `≥ p + ε` for `τ_i ∉ T̂_i`;
`β̂_j(τ_j)[T̂_{-i,j} | T̂_i] ≥ p + ε` for `τ_j ∈ T̂_j` and `≤ p − ε` for `τ_j ∉ T̂_j`.
If the direct mechanism `(T, q, t)` is Bayesian incentive-compatible (`t_k` is the transfer paid
by agent `k`), then so is `(T, q, t̃)`, where `t̃_k = t_k` for `k ≠ i, j`; if `τ_i ∈ T̂_i` and
`τ_j ∈ T̂_j`, agent `i` pays one dollar to `j` when `τ_{-i,j} ∈ T̂_{-i,j}`
(`t̃_i = t_i + 1`, `t̃_j = t_j − 1`) and `j` pays `c_i` dollars to `i` otherwise
(`t̃_i = t_i − c_i`, `t̃_j = t_j + c_i`); otherwise `t̃_i = t_i`, `t̃_j = t_j`; and
`(p − ε)/(1 − (p − ε)) < c_i < (p + ε)/(1 − (p + ε))`.
The printed (v) has the opposite signs (`t̃_i = t_i − 1`, …), which with `t_i` a payment makes
the bet attractive to exactly the types outside `T̂_i`, `T̂_j` and the conclusion false; the signs
here are those of the bet described in the text on p.186. -/
theorem betting_preserves_bic {ι : Type} [Fintype ι] [DecidableEq ι] {Θ T : ι → Type*}
    {A : Type*} (ts : TypeSpace Θ T) (vu : ι → A → (∀ i, Θ i) → ℝ)
    (hN : 3 ≤ Fintype.card ι) (i j : ι) (hij : i ≠ j) (p ε : ℝ)
    (hp : p ∈ Set.Ioo (0 : ℝ) 1) (hε : ε ∈ Set.Ioo (0 : ℝ) 1)
    (Ti : Set (T i)) (Tj : Set (T j)) (Tij : Set (∀ k : {k : ι // k ≠ i ∧ k ≠ j}, T k))
    (hTij : Tij ≠ Set.univ)
    (h1i : ∀ τi : T i, 0 < (ts.β i τi).toOuterMeasure {τo | τo ⟨j, hij.symm⟩ ∈ Tj})
    (h1j : ∀ τj : T j, 0 < (ts.β j τj).toOuterMeasure {τo | τo ⟨i, hij⟩ ∈ Ti})
    (h2i_in : ∀ τi ∈ Ti, (condProb (ts.β i τi) {τo | (fun k : {k : ι // k ≠ i ∧ k ≠ j} => τo ⟨k.1, k.2.1⟩) ∈ Tij}
      {τo | τo ⟨j, hij.symm⟩ ∈ Tj}).toReal ≤ p - ε)
    (h2i_out : ∀ τi ∉ Ti, p + ε ≤ (condProb (ts.β i τi) {τo | (fun k : {k : ι // k ≠ i ∧ k ≠ j} => τo ⟨k.1, k.2.1⟩) ∈ Tij}
      {τo | τo ⟨j, hij.symm⟩ ∈ Tj}).toReal)
    (h2j_in : ∀ τj ∈ Tj, p + ε ≤ (condProb (ts.β j τj) {τo | (fun k : {k : ι // k ≠ i ∧ k ≠ j} => τo ⟨k.1, k.2.2⟩) ∈ Tij}
      {τo | τo ⟨i, hij⟩ ∈ Ti}).toReal)
    (h2j_out : ∀ τj ∉ Tj, (condProb (ts.β j τj) {τo | (fun k : {k : ι // k ≠ i ∧ k ≠ j} => τo ⟨k.1, k.2.2⟩) ∈ Tij}
      {τo | τo ⟨i, hij⟩ ∈ Ti}).toReal ≤ p - ε)
    (q : (∀ k, T k) → A) (t : ι → (∀ k, T k) → ℝ)
    (hbic : IsBayesEq ts (qlUtility vu) (qlDirect ts q t) (truthful T))
    (c : ℝ) (hc : (p - ε) / (1 - (p - ε)) < c ∧ c < (p + ε) / (1 - (p + ε)))
    (t' : ι → (∀ k, T k) → ℝ)
    (h4 : ∀ k, k ≠ i → k ≠ j → t' k = t k)
    (h5in : ∀ τ : ∀ k, T k, τ i ∈ Ti → τ j ∈ Tj → (fun k : {k : ι // k ≠ i ∧ k ≠ j} => τ k) ∈ Tij →
      t' i τ = t i τ + 1 ∧ t' j τ = t j τ - 1)
    (h5out : ∀ τ : ∀ k, T k, τ i ∈ Ti → τ j ∈ Tj → (fun k : {k : ι // k ≠ i ∧ k ≠ j} => τ k) ∉ Tij →
      t' i τ = t i τ - c ∧ t' j τ = t j τ + c)
    (h6 : ∀ τ : ∀ k, T k, (τ i ∉ Ti ∨ τ j ∉ Tj) → t' i τ = t i τ ∧ t' j τ = t j τ) :
    IsBayesEq ts (qlUtility vu) (qlDirect ts q t') (truthful T) := by sorry

end MechanismDesign.Robust

