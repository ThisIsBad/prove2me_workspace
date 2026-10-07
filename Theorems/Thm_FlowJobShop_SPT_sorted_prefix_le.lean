import Mathlib

namespace FlowJobShop.SPT

/-- Prefix sums are smallest in sorted order: if `σ` lists `Fin n` so that `L (σ 0) ≤ L (σ 1) ≤ ⋯`,
then for every bijection `ρ` and every `k`, `∑_{j ≤ k} L_{σ j} ≤ ∑_{j ≤ k} L_{ρ j}`
(Gonzalez–Sahni 1978, proof of Lemma 9, p. 47: `∑_{j=1}^k L_{i_j}/m ≥ ∑_{j=1}^k L_j/m`). -/
theorem sorted_prefix_le {n : ℕ} (L : Fin n → ℝ) (σ : Fin n ≃ Fin n)
    (hσ : Monotone fun k => L (σ k)) (ρ : Fin n ≃ Fin n) (k : Fin n) :
    ∑ j ∈ Finset.Iic k, L (σ j) ≤ ∑ j ∈ Finset.Iic k, L (ρ j) := by sorry

end FlowJobShop.SPT

