import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P39

namespace QAlgorithms.Papers.Independent.Support50.P39

noncomputable section

open QAlgorithms

open Filter Topology

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:quant-ph/0106080v3, PDF pp.4--6, Eqs. (9)--(13): the finite
Holevo objective H_d equals log2 d plus optimized clipped coherent information,
and an optimal CPTP map and d^2-element unitary encoding attain it.
The SAME twirling family gives, for EVERY preprocessing map, the signed
per-map identity chi=log2 d+S(B^n)-S(sigma). Clipping is used only at the
optimized value. This includes d=1 (both sides zero) and does not identify
H_d with the unrestricted fixed-(d,n) operational capacity. -/
theorem finiteHolevoOptimization {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho)
    (n d : ℕ) (hn : 0 < n) (hd : 0 < d) :
    denseCodingHolevoValue rho n d = Real.logb 2 d + finiteCoherentOpt rho n d ∧
    ∃ Phi : Superop (Fin n → A) (Fin d), IsChannel Phi ∧
      clippedCoherentInformation (aliceAction Phi (noisyResourceCopies rho n)) =
        finiteCoherentOpt rho n d ∧
      ∃ U : Fin (d*d) → Matrix.unitaryGroup (Fin d) ℂ,
        TracelessTwirling U ∧
        (∀ Psi : Superop (Fin n → A) (Fin d), IsChannel Psi →
          IsEncoding (uniformWeight d) (unitaryEncoders Psi U) ∧
          encodingHolevo rho n (uniformWeight d) (unitaryEncoders Psi U) =
            Real.logb 2 d + vnEntropy (traceLeft (noisyResourceCopies rho n)) -
              vnEntropy (aliceAction Psi (noisyResourceCopies rho n))) ∧
        encodingHolevo rho n (uniformWeight d) (unitaryEncoders Phi U) =
          denseCodingHolevoValue rho n d := by sorry

end

end QAlgorithms.Papers.Independent.Support50.P39

