import Mathlib

namespace ThreeOpSplitting.ConvexRates

/-- The three-operator map of Eq. (1.2) specialised to problem (3.1):
`T z = prox_{γf}(2 prox_{γg} z - z - γ ∇h(prox_{γg} z)) + z - prox_{γg} z`.
Here `proxf`, `proxg`, `gradh` stand for `prox_{γf}`, `prox_{γg}`, `∇h`. -/
noncomputable def splittingOp {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (proxf proxg gradh : H → H) (γ : ℝ) (z : H) : H :=
  proxf ((2 : ℝ) • proxg z - z - γ • gradh (proxg z)) + z - proxg z

/-- The sequence `(z^k)` of Algorithm 2 with relaxation `λ_k ≡ 1`, started at `z⁰`:
`z^{k+1} = z^k + (x^k_f - x^k_g)` with `x^k_g = prox_{γg}(z^k)` and
`x^k_f = prox_{γf}(2x^k_g - z^k - γ∇h(x^k_g))`. -/
noncomputable def algZ {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (proxf proxg gradh : H → H) (γ : ℝ) (z0 : H) : ℕ → H
  | 0 => z0
  | k + 1 =>
      algZ proxf proxg gradh γ z0 k +
        (proxf ((2 : ℝ) • proxg (algZ proxf proxg gradh γ z0 k) - algZ proxf proxg gradh γ z0 k
            - γ • gradh (proxg (algZ proxf proxg gradh γ z0 k)))
          - proxg (algZ proxf proxg gradh γ z0 k))

/-- Step 1 of Algorithm 2: `x^k_g = prox_{γg}(z^k)`. -/
noncomputable def algXg {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (proxf proxg gradh : H → H) (γ : ℝ) (z0 : H) (k : ℕ) : H :=
  proxg (algZ proxf proxg gradh γ z0 k)

/-- Step 2 of Algorithm 2: `x^k_f = prox_{γf}(2x^k_g - z^k - γ∇h(x^k_g))`. -/
noncomputable def algXf {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (proxf proxg gradh : H → H) (γ : ℝ) (z0 : H) (k : ℕ) : H :=
  proxf ((2 : ℝ) • algXg proxf proxg gradh γ z0 k - algZ proxf proxg gradh γ z0 k
    - γ • gradh (algXg proxf proxg gradh γ z0 k))

/-- The weighted ergodic iterate `x̄^k = 2/((k+1)(k+2)) ∑_{i=0}^k (i+1) x^i` (§3.2). -/
noncomputable def weightedErgodic {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (x : ℕ → H) (k : ℕ) : H :=
  (2 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) •
    ∑ i ∈ Finset.range (k + 1), ((i : ℝ) + 1) • x i

end ThreeOpSplitting.ConvexRates
