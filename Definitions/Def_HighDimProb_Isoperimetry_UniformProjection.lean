import Mathlib

open MeasureTheory

namespace HighDimProb.Isoperimetry

/-- `P` is a random orthogonal projection in `ℝⁿ` onto an `m`-dimensional subspace uniformly
distributed in the Grassmannian `G_{n,m}`. Vershynin, *High-Dimensional Probability* (2018),
§5.2.6/§5.3, defines a random `m`-dimensional subspace `E ∼ Unif(G_{n,m})` operationally by
rotation invariance of its distribution (`P` is a measurable random operator, so its law is
a genuine probability measure on the operator space): `P {E ∈ 𝓔} = P {U(E) ∈ 𝓔}` for every orthogonal
matrix `U` and every fixed set `𝓔 ⊂ G_{n,m}`. This definition states the same property for the
orthogonal projection `P` onto `E` directly (as the book's own statements, e.g. Theorem 5.3.1
and Lemma 5.3.2, are phrased in terms of `P` rather than `E` itself): `P ω` is, for almost
every `ω`, an orthogonal projection (idempotent and self-adjoint) of rank `m`, and the law of
`P` is invariant under conjugation `p ↦ U ∘ p ∘ U⁻¹` by every orthogonal transformation `U` —
exactly the transformation a projection onto `E` undergoes when `E` is replaced by `U(E)`. -/
def IsUniformProjection {Ω : Type} [MeasurableSpace Ω] (Prob : Measure Ω) {n : ℕ} (m : ℕ)
    (P : Ω → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) : Prop :=
  Measurable P ∧
  (∀ᵐ ω ∂Prob, IsIdempotentElem (P ω)) ∧
  (∀ᵐ ω ∂Prob, IsSelfAdjoint (P ω)) ∧
  (∀ᵐ ω ∂Prob,
    Module.finrank ℝ (LinearMap.range (P ω : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))) = m) ∧
  (∀ U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
    Measure.map
      (fun ω => (U.toContinuousLinearEquiv : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).comp
        ((P ω).comp (U.symm.toContinuousLinearEquiv : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))))
      Prob
    = Measure.map P Prob)

end HighDimProb.Isoperimetry
