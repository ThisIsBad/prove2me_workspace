import Mathlib
open scoped BoundedContinuousFunction

namespace IntLInfty.Kan

/-- The `m`-simplex in corner coordinates: `Δᵐ = {t ∈ ℝᵐ | tᵢ ≥ 0, ∑ tᵢ ≤ 1}`. -/
def simplex (m : ℕ) : Set (Fin m → ℝ) := {t | (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ 1}

theorem isCompact_simplex (m : ℕ) : IsCompact (simplex m) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · have h1 : IsClosed {t : Fin m → ℝ | ∀ i, 0 ≤ t i} := by
      simpa only [Set.ofPred_forall] using
        isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
    have h2 : IsClosed {t : Fin m → ℝ | ∑ i, t i ≤ 1} :=
      isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
    exact h1.inter h2
  · refine (Metric.isBounded_closedBall (x := (0 : Fin m → ℝ)) (r := 1)).subset ?_
    intro t ht
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (ht.1 i)]
    exact (Finset.single_le_sum (fun j _ => ht.1 j) (Finset.mem_univ i)).trans ht.2

instance (m : ℕ) : CompactSpace (simplex m) :=
  isCompact_iff_compactSpace.mp (isCompact_simplex m)

/-- The vertices of `Δᵐ`: `v₀ = 0` and `v_{k+1} = e_k`. -/
def vertex (m : ℕ) : Fin (m + 1) → (Fin m → ℝ) :=
  Fin.cases 0 fun k => Pi.single k 1

/-- The linear part of the affine coface map `dⁱ : Δᵐ → Δᵐ⁺¹`. -/
noncomputable def cofaceLin (m : ℕ) (i : Fin (m + 2)) : (Fin m → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ) :=
  (Matrix.of fun (a : Fin (m + 1)) (k : Fin m) =>
    (vertex (m + 1) (i.succAbove k.succ) - vertex (m + 1) (i.succAbove 0)) a).mulVecLin

/-- The affine coface map `dⁱ : Δᵐ → Δᵐ⁺¹` sending the vertex `vₖ` to `v_{dⁱ(k)}`, where
`dⁱ(k) = k` for `k < i` and `k + 1` for `k ≥ i` (equation (3), i.e. `Fin.succAbove i`). -/
noncomputable def coface (m : ℕ) (i : Fin (m + 2)) (x : Fin m → ℝ) : Fin (m + 1) → ℝ :=
  vertex (m + 1) (i.succAbove 0) + cofaceLin m i x

/-- Differential forms on (a neighbourhood of) `Δᵐ`: functions with values in the exterior algebra of
`(ℝᵐ)∗`; the wedge product is the pointwise product. Only the values on `Δᵐ` are ever used. -/
abbrev Ω (m : ℕ) : Type := (Fin m → ℝ) → ExteriorAlgebra ℝ (Module.Dual ℝ (Fin m → ℝ))

/-- The coordinate one-form `dxₖ`. -/
noncomputable def dx (m : ℕ) (k : Fin m) : ExteriorAlgebra ℝ (Module.Dual ℝ (Fin m → ℝ)) :=
  ExteriorAlgebra.ι ℝ (LinearMap.proj k)

/-- The basis `dx_I = dx_{i₁} ∧ ⋯ ∧ dx_{iₚ}` (`I = {i₁ < ⋯ < iₚ}`) of the exterior algebra. -/
noncomputable def formBasis (m : ℕ) :
    Module.Basis (Finset (Fin m)) ℝ (ExteriorAlgebra ℝ (Module.Dual ℝ (Fin m → ℝ))) :=
  ((Pi.basisFun ℝ (Fin m)).dualBasis).ExteriorAlgebra

/-- The coefficient function `c_I` of a form `ω = ∑_I c_I dx_I`. -/
noncomputable def coeff {m : ℕ} (ω : Ω m) (I : Finset (Fin m)) : (Fin m → ℝ) → ℝ :=
  fun x => (formBasis m).repr (ω x) I

/-- The exterior derivative on `Δᵐ`: `d(∑_I c_I dx_I) = ∑_k ∑_I ∂ₖc_I dxₖ ∧ dx_I`, the partial
derivatives taken within `Δᵐ` (one-sided at the boundary). -/
noncomputable def extD {m : ℕ} (ω : Ω m) : Ω m := fun x =>
  ∑ k : Fin m, dx m k *
    ∑ I : Finset (Fin m),
      (fderivWithin ℝ (coeff ω I) (simplex m) x (Pi.single k 1)) • formBasis m I

/-- `ω` is an `n`-form on `Δᵐ`. -/
def IsDeg {m : ℕ} (n : ℕ) (ω : Ω m) : Prop :=
  ∀ x ∈ simplex m, ω x ∈ ⋀[ℝ]^n (Module.Dual ℝ (Fin m → ℝ))

/-- `ω ∈ Γ_{Cʳ}` and `dω ∈ Γ_{Cʳ}` on `Δᵐ` (Convention 5.1). -/
def IsCr {m : ℕ} (r : ℕ) (ω : Ω m) : Prop :=
  ∀ I, ContDiffOn ℝ r (coeff ω I) (simplex m) ∧ ContDiffOn ℝ r (coeff (extD ω) I) (simplex m)

/-- `ω` is closed on `Δᵐ`. -/
def IsClosedForm {m : ℕ} (ω : Ω m) : Prop := ∀ x ∈ simplex m, extD ω x = 0

/-- Pullback of forms along the affine coface `dⁱ : Δᵐ → Δᵐ⁺¹`. -/
noncomputable def pull (m : ℕ) (i : Fin (m + 2)) (ω : Ω (m + 1)) : Ω m := fun x =>
  ExteriorAlgebra.map (cofaceLin m i).dualMap (ω (coface m i x))

/-- The Banach space of `r`-jets of the coefficients on `Δᵐ`: for every multi-index `I`, every order
`k ≤ r` and every `β : Fin k → Fin m` (the partial derivative `∂_{β 1} ⋯ ∂_{β k}`), a bounded
continuous function on `Δᵐ`, with the sup norm. -/
def Jet (r m : ℕ) : Type :=
  (I : Finset (Fin m)) → (k : Fin (r + 1)) → (Fin (k : ℕ) → Fin m) → (simplex m →ᵇ ℝ)

noncomputable instance (r m : ℕ) : NormedAddCommGroup (Jet r m) :=
  inferInstanceAs (NormedAddCommGroup
    ((I : Finset (Fin m)) → (k : Fin (r + 1)) → (Fin (k : ℕ) → Fin m) → (simplex m →ᵇ ℝ)))

noncomputable instance (r m : ℕ) : NormedSpace ℝ (Jet r m) :=
  inferInstanceAs (NormedSpace ℝ
    ((I : Finset (Fin m)) → (k : Fin (r + 1)) → (Fin (k : ℕ) → Fin m) → (simplex m →ᵇ ℝ)))

open Classical in
/-- The partial derivative `∂_{β 1} ⋯ ∂_{β k} f` within `Δᵐ`, restricted to `Δᵐ` (it is continuous
for every `Cʳ` function, `k ≤ r`; the guard only avoids proving this inside the definition). -/
noncomputable def jetComp {m : ℕ} (f : (Fin m → ℝ) → ℝ) (k : ℕ) (β : Fin k → Fin m) :
    simplex m →ᵇ ℝ :=
  if h : ContinuousOn (fun x => iteratedFDerivWithin ℝ k f (simplex m) x fun l => Pi.single (β l) 1)
      (simplex m) then
    BoundedContinuousFunction.mkOfCompact ⟨_, h.domRestrict⟩
  else 0

/-- The `Cʳ` jet of a form and of its exterior derivative: this embeds `Ωⁿ_{Cʳ}(Δᵐ)` in a Banach
space with the `Cʳ` topology on `α` and on `dα`. -/
noncomputable def jet (r : ℕ) {m : ℕ} (ω : Ω m) : Jet r m × Jet r m :=
  (fun I k β => jetComp (coeff ω I) k β, fun I k β => jetComp (coeff (extD ω) I) k β)

/-- The Banach space `Ωⁿ_{Cʳ}(Δᵐ)` (Convention 5.1), as the closed subspace of `Jet r m × Jet r m`
spanned by the jets of `Cʳ` `n`-forms `α` with `dα` of class `Cʳ`. -/
noncomputable def CrForms (r m n : ℕ) : Submodule ℝ (Jet r m × Jet r m) :=
  (Submodule.span ℝ (jet r '' {ω : Ω m | IsDeg n ω ∧ IsCr r ω})).topologicalClosure

/-- The Banach space `Ωⁿ_{closed}(Δᵐ)` of closed `Cʳ` `n`-forms, the same way. -/
noncomputable def CrClosed (r m n : ℕ) : Submodule ℝ (Jet r m × Jet r m) :=
  (Submodule.span ℝ (jet r '' {ω : Ω m | IsDeg n ω ∧ IsCr r ω ∧ IsClosedForm ω})).topologicalClosure

open Classical in
/-- An operator `F` on forms, applied to the point `w` of the jet space through a representative
`Cʳ` `n`-form `ω` with `jet ω = w`, landing in the subspace `V`. -/
noncomputable def viaRep {r m m' : ℕ} (n : ℕ) (V : Submodule ℝ (Jet r m' × Jet r m'))
    (F : Ω m → Ω m') (w : Jet r m × Jet r m) : V :=
  if h : ∃ ω : Ω m, IsDeg n ω ∧ IsCr r ω ∧ jet r ω = w ∧ jet r (F ω) ∈ V then
    ⟨jet r (F h.choose), h.choose_spec.2.2.2⟩
  else 0

/-- The face map `dᵢ : Ωⁿ_{Cʳ}(Δᵐ⁺¹) → Ωⁿ_{Cʳ}(Δᵐ)`, restriction along the `i`-th coface. -/
noncomputable def faceCr (r m n : ℕ) (i : Fin (m + 2)) (w : CrForms r (m + 1) n) : CrForms r m n :=
  viaRep n (CrForms r m n) (pull m i) w

/-- The face map `dᵢ : Ωⁿ_{closed}(Δᵐ⁺¹) → Ωⁿ_{closed}(Δᵐ)`. -/
noncomputable def faceCl (r m n : ℕ) (i : Fin (m + 2)) (w : CrClosed r (m + 1) n) : CrClosed r m n :=
  viaRep n (CrClosed r m n) (pull m i) w

/-- The exterior derivative `d : Ωⁿ_{Cʳ}(Δᵐ) → Ωⁿ⁺¹_{closed}(Δᵐ)`. -/
noncomputable def dCr (r m n : ℕ) (w : CrForms r m n) : CrClosed r m (n + 1) :=
  viaRep n (CrClosed r m (n + 1)) extD w

end IntLInfty.Kan
