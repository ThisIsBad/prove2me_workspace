import Mathlib

namespace RobustMDP.Discounted

/-- Lemma 2 (Nilim–El Ghaoui 2005, p. 785), in the corrected form the proof of Theorem 3 uses.
Let `q ∈ ℝⁿ₊` and let `g : ℝⁿ → ℝⁿ` be componentwise nondecreasing and a contraction in the sup
norm (`ContractingWith K g`, i.e. `K < 1` and `g` is `K`-Lipschitz for the sup metric of
`Fin n → ℝ`). Consider problem (24): maximise `qᵀ v` subject to `v ≤ g(v)` componentwise.
Then `g` has a unique fixed point `v_∞`, and
1. `qᵀ v_∞` is the maximum of (24) (attained at the feasible point `v_∞`);
2. every feasible `v` satisfies `v ≤ v_∞` componentwise;
3. if moreover `q > 0` componentwise, `v_∞` is the only optimizer of (24).

As printed, the lemma claims a unique optimizer for every `q ∈ ℝⁿ₊`; that fails when `q` has zero
entries (`g ≡ 0`, `q = (1, 0)`: every `(0, -t)`, `t ≥ 0`, is optimal), so uniqueness of the
optimizer is stated under `q > 0`. The printed feasibility hypothesis is automatic. -/
theorem lemma_two {n : ℕ} (q : Fin n → ℝ) (hq : 0 ≤ q) (g : (Fin n → ℝ) → (Fin n → ℝ))
    (hmono : Monotone g) (K : NNReal) (hg : ContractingWith K g) :
    ∃ vinf : Fin n → ℝ,
      g vinf = vinf ∧ (∀ w, g w = w → w = vinf) ∧
      IsGreatest ((fun v : Fin n → ℝ => ∑ i, q i * v i) '' {v | v ≤ g v})
        (∑ i, q i * vinf i) ∧
      (∀ v, v ≤ g v → v ≤ vinf) ∧
      ((∀ i, 0 < q i) →
        ∀ v, v ≤ g v → ∑ i, q i * v i = ∑ i, q i * vinf i → v = vinf) := by sorry

end RobustMDP.Discounted
