import Mathlib
import Definitions.Def_SAGA_Convex_finiteSum

namespace SAGA.Convex

/-- The point `w^{k+1}` of eq. (1) (p. 2) for the state `s = (x^k, φ^k)` and the sampled index
`j`: `w = x^k - γ (f′_j(x^k) - f′_j(φ_j^k) + (1/n) ∑ᵢ f′ᵢ(φᵢ^k))`. The table average uses the old
table `φ^k`. -/
noncomputable def sagaW {d n : ℕ}
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (γ : ℝ)
    (s : EuclideanSpace ℝ (Fin d) × (Fin n → EuclideanSpace ℝ (Fin d))) (j : Fin n) :
    EuclideanSpace ℝ (Fin d) :=
  s.1 - γ • (f' j s.1 - f' j (s.2 j) + (1 / (n : ℝ)) • ∑ i, f' i (s.2 i))

/-- One SAGA iteration (p. 2, steps 1–3 and eqs. (1)–(2)) from the state `s = (x^k, φ^k)` with
the index `j`: the new iterate is `x^{k+1} = P(w^{k+1})`, where `P` plays the role of
`prox_γ^h`, and the table entry `j` is overwritten by `x^k`, all other entries unchanged. -/
noncomputable def sagaStep {d n : ℕ}
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (γ : ℝ)
    (s : EuclideanSpace ℝ (Fin d) × (Fin n → EuclideanSpace ℝ (Fin d))) (j : Fin n) :
    EuclideanSpace ℝ (Fin d) × (Fin n → EuclideanSpace ℝ (Fin d)) :=
  (P (sagaW f' γ s j), Function.update s.2 j s.1)

/-- The gradient-estimation error `Δ = -(1/γ)(w^{k+1} - x^k) - f′(x^k)` (Appendix C, p. 11) for
the state `s = (x^k, φ^k)` and the index `j`. -/
noncomputable def sagaDelta {d n : ℕ}
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (γ : ℝ)
    (s : EuclideanSpace ℝ (Fin d) × (Fin n → EuclideanSpace ℝ (Fin d))) (j : Fin n) :
    EuclideanSpace ℝ (Fin d) :=
  -(1 / γ) • (sagaW f' γ s j - s.1) - gradAvg f' s.1

end SAGA.Convex
