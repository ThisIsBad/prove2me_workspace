import Mathlib

/-!
# K-secant planes to the even spinor variety of an abelian `n`-fold

E. Markman, *Cycles on abelian 2n-folds of Weil type from secant sheaves on abelian n-folds*,
arXiv:2502.03415v2, §1.2, §2.1, §2.2 and §2.4.

Linear-algebra model of the objects of §2.  `X` is a complex torus of dimension `n`.

* `H¹(X, ℂ) = ℂ^{2n}` (`H1`), with rational points `ℚ^{2n}` and integral points `ℤ^{2n}`
  (coordinates with respect to a basis `e₁, …, e_{2n}` of `H¹(X, ℤ)`).
* `S_ℂ = H^*(X, ℂ) = ∧^* H¹(X, ℂ)` (`Spinor`), the spin representation; its even part is `S_ℂ^+`.
* `H¹(X̂, ℂ) ≅ H¹(X, ℂ)^*` is written in the dual coordinates, so that
  `V_ℂ = H¹(X, ℂ) ⊕ H¹(X̂, ℂ) = ℂ^{2n} ⊕ ℂ^{2n}` (`VC`), with the pairing (1.2.2)
  `((w₁, t₁), (w₂, t₂))_V = t₁(w₂) + t₂(w₁)` (`pairV`).
* `m_{(w,t)} = L_w + D_t` (2.1.2): exterior multiplication by `w` plus contraction with `t`
  (`cliffAt s : v ↦ m_v(s)`).  An even pure spinor is a nonzero `s ∈ S_ℂ^+` whose annihilator
  `{v ∈ V_ℂ | m_v(s) = 0}` (`annih`) is `2n`-dimensional, i.e. maximal isotropic.
* The complex structure of `X` is a real matrix `J` with `J² = -1` acting on `H¹(X, ℝ)`; its
  `i`-eigenspace is `H^{1,0}(X)`.  `z ∈ ℂ^×` acts on `H¹(X, ℂ)` by `Re z + Im z · J` and on
  `H^k(X, ℂ)` through `∧^k`; a class of type `(p, q)` is multiplied by `z^p z̄^q`.
* The complex structure of `V_ℝ` is `I = J ⊕ (-Jᵀ)`, the extension of `J` on `H¹(X, ℝ)` that is
  an isometry of `(·,·)_V` (Markman, footnote 8); `V^{1,0}` and `V^{0,1}` are its
  `±i`-eigenspaces.
-/

noncomputable section

namespace MarkmanSecant

open scoped ExteriorAlgebra

/-! ### Cohomology of `X` and the lattice `V` -/

/-- `H¹(X, ℂ) = ℂ^{2n}`. -/
abbrev H1 (n : ℕ) := Fin (2 * n) → ℂ

/-- The spin representation `S_ℂ = H^*(X, ℂ) = ∧^* H¹(X, ℂ)`. -/
abbrev Spinor (n : ℕ) := ExteriorAlgebra ℂ (H1 n)

/-- Index set of `V = H¹(X) ⊕ H¹(X̂)`: `Sum.inl i` is the `i`-th coordinate of `H¹(X)`,
`Sum.inr i` the `i`-th (dual) coordinate of `H¹(X̂) ≅ H¹(X)^*`. -/
abbrev VIdx (n : ℕ) := Fin (2 * n) ⊕ Fin (2 * n)

/-- `V_ℂ = H¹(X, ℂ) ⊕ H¹(X̂, ℂ)`. -/
abbrev VC (n : ℕ) := VIdx n → ℂ

variable {n : ℕ}

/-- The `H¹(X)`-component `w` of `v = (w, t) ∈ V_ℂ`. -/
def wPart (v : VC n) : H1 n := fun i => v (Sum.inl i)

/-- The `H¹(X̂)`-component `t` of `v = (w, t) ∈ V_ℂ`. -/
def tPart (v : VC n) : H1 n := fun i => v (Sum.inr i)

/-- The symmetric pairing (1.2.2): `((w₁, t₁), (w₂, t₂))_V = t₁(w₂) + t₂(w₁)`. -/
def pairV (x y : VC n) : ℂ := tPart x ⬝ᵥ wPart y + tPart y ⬝ᵥ wPart x

/-- A vector of `V_ℚ`, viewed in `V_ℂ`. -/
def ratV (x : VIdx n → ℚ) : VC n := fun i => ((x i : ℚ) : ℂ)

/-- A vector of `V_ℝ`, viewed in `V_ℂ`. -/
def realV (x : VIdx n → ℝ) : VC n := fun i => ((x i : ℝ) : ℂ)

/-- A rational endomorphism of `V_ℚ` (a matrix), acting on `V_ℂ`. -/
def ratMatV (F : Matrix (VIdx n) (VIdx n) ℚ) : Matrix (VIdx n) (VIdx n) ℂ :=
  F.map (fun q => ((q : ℚ) : ℂ))

/-! ### The Clifford action and pure spinors -/

/-- The projection `v = (w, t) ↦ w` onto `H¹(X, ℂ)`, as a linear map. -/
def wPartLin : VC n →ₗ[ℂ] H1 n := LinearMap.funLeft ℂ ℂ Sum.inl

/-- The projection `v = (w, t) ↦ t` onto `H¹(X̂, ℂ)`, as a linear map. -/
def tPartLin : VC n →ₗ[ℂ] H1 n := LinearMap.funLeft ℂ ℂ Sum.inr

/-- The identification `H¹(X̂, ℂ) ≅ H¹(X, ℂ)^*`: `t ↦ (w ↦ ∑ᵢ tᵢ wᵢ)`. -/
def dualLin : H1 n →ₗ[ℂ] Module.Dual ℂ (H1 n) :=
  ∑ i, (LinearMap.proj i : H1 n →ₗ[ℂ] ℂ).smulRight (LinearMap.proj i : Module.Dual ℂ (H1 n))

/-- The element `t ∈ H¹(X̂, ℂ) ≅ H¹(X, ℂ)^*` as a linear functional on `H¹(X, ℂ)`. -/
def dualOf (t : H1 n) : Module.Dual ℂ (H1 n) := dualLin t

/-- For a fixed spinor `s`, the map `m_s : V_ℂ → S_ℂ`, `v = (w, t) ↦ m_v(s) = w ∧ s + D_t(s)`:
the Clifford action (2.1.2) `m_v = L_w + D_t` (exterior multiplication by `w` plus contraction
with `t`) applied to `s`. -/
def cliffAt (s : Spinor n) : VC n →ₗ[ℂ] Spinor n :=
  LinearMap.mulRight ℂ s ∘ₗ ExteriorAlgebra.ι ℂ ∘ₗ wPartLin +
    (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (H1 n)))).flip s ∘ₗ dualLin ∘ₗ tPartLin

/-- The annihilator `{v ∈ V_ℂ | m_v(s) = 0}` of a spinor `s` (the kernel of `m_s`). -/
def annih (s : Spinor n) : Submodule ℂ (VC n) := LinearMap.ker (cliffAt s)

/-- The even part `S_ℂ^+ = ⊕_i H^{2i}(X, ℂ)`. -/
def evenSpinors (n : ℕ) : Submodule ℂ (Spinor n) :=
  ⨆ k : ℕ, ⋀[ℂ]^(2 * k) (H1 n)

/-- An even pure spinor: a nonzero `s ∈ S_ℂ^+` whose annihilator in `V_ℂ` is a subspace of
dimension `2n` (a maximal isotropic subspace of the `4n`-dimensional `V_ℂ`). -/
def IsEvenPureSpinor (s : Spinor n) : Prop :=
  s ∈ evenSpinors n ∧ s ≠ 0 ∧ Module.finrank ℂ (annih s) = 2 * n

/-! ### Rational and integral classes -/

/-- The monomial `e_{i₁} ∧ ⋯ ∧ e_{i_k}` in the standard basis of `H¹(X, ℤ)`. -/
def monomial (l : List (Fin (2 * n))) : Spinor n :=
  (l.map fun i => ExteriorAlgebra.ι ℂ (Pi.single i (1 : ℂ))).prod

/-- `s ∈ H^*(X, ℤ)`: an integral combination of monomials in the basis of `H¹(X, ℤ)`. -/
def IsIntegralClass (s : Spinor n) : Prop :=
  s ∈ Submodule.span ℤ (Set.range (monomial (n := n)))

/-- `s ∈ H^*(X, ℚ)`: some positive integer multiple of `s` is integral. -/
def IsRationalClass (s : Spinor n) : Prop :=
  ∃ m : ℕ, 0 < m ∧ IsIntegralClass ((m : ℂ) • s)

/-! ### Hodge structures -/

/-- The complex matrix of a real matrix. -/
def cMat (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ :=
  J.map (fun r => ((r : ℝ) : ℂ))

/-- The action of `z ∈ ℂ` on `H¹(X, ℂ)` through the complex structure `J`: `Re z + Im z · J`.
It is multiplication by `z` on `H^{1,0}` (the `i`-eigenspace of `J`) and by `z̄` on `H^{0,1}`. -/
def scal (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (z : ℂ) : H1 n →ₗ[ℂ] H1 n :=
  z.re • LinearMap.id + z.im • Matrix.mulVecLin (cMat J)

/-- `s ∈ H^*(X, ℂ)` is of Hodge type `(p, q)`: `∧^*(Re z + Im z · J)(s) = z^p z̄^q s` for all
`z ∈ ℂ`. -/
def HasHodgeType (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (p q : ℕ) (s : Spinor n) : Prop :=
  ∀ z : ℂ, ExteriorAlgebra.map (scal J z) s = (z ^ p * (starRingEnd ℂ z) ^ q) • s

/-- `s` lies in the (rational) Hodge ring `⊕_p H^{p,p}(X, ℚ)` of `X`. -/
def IsInHodgeRing (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (s : Spinor n) : Prop :=
  ∃ c : ℕ → Spinor n, (∀ p, IsRationalClass (c p) ∧ HasHodgeType J p p (c p)) ∧
    s = ∑ p ∈ Finset.range (n + 1), c p

/-- The complex structure `I = J ⊕ (-Jᵀ)` of `V_ℝ = H¹(X, ℝ) ⊕ H¹(X̂, ℝ)` (the complex
structure of `X × X̂`), as a matrix acting on `V_ℂ`. -/
def IV (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) : Matrix (VIdx n) (VIdx n) ℂ :=
  Matrix.fromBlocks (cMat J) 0 0 (-(cMat J).transpose)

/-- `V^{1,0}`: the `i`-eigenspace of `I` in `V_ℂ`. -/
def V10 (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) : Submodule ℂ (VC n) :=
  LinearMap.ker ((IV J).mulVecLin - Complex.I • LinearMap.id)

/-- `V^{0,1}`: the `(-i)`-eigenspace of `I` in `V_ℂ`. -/
def V01 (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) : Submodule ℂ (VC n) :=
  LinearMap.ker ((IV J).mulVecLin + Complex.I • LinearMap.id)

/-! ### The ample class, the contraction `θ`, and `exp(u)` -/

/-- `Θ(a, b) = ⟨Θ, a ∧ b⟩` for `Θ ∈ H²(X)` and `a, b ∈ H¹(X̂) ≅ H¹(X)^*`, computed as the
iterated contraction `D_b D_a Θ` (so `⟨e_i ∧ e_j, a ∧ b⟩ = a_i b_j - a_j b_i`). -/
def formEval (Θ : Spinor n) (a b : H1 n) : ℂ :=
  ExteriorAlgebra.algebraMapInv
    (CliffordAlgebra.contractLeft (dualOf b) (CliffordAlgebra.contractLeft (dualOf a) Θ))

/-- The contraction (2.4.3) `θ : H¹(X̂) ≅ H¹(X)^* → H¹(X)`, `θ(y) = D_y Θ`. -/
def theta (Θ : Spinor n) (y : H1 n) : H1 n :=
  ExteriorAlgebra.ιInv (CliffordAlgebra.contractLeft (dualOf y) Θ)

/-- A real vector of `H¹(X̂, ℝ)`, viewed in `H¹(X̂, ℂ)`. -/
def realH1 (a : Fin (2 * n) → ℝ) : H1 n := fun i => ((a i : ℝ) : ℂ)

/-- `Θ ∈ H^{1,1}(X, ℤ)` is an ample class, with the sign convention used in the proof of
Proposition 2.4.4: `Θ(a ∧ I(a)) > 0` for every nonzero `a ∈ H¹(X̂, ℝ)`, where `I = -Jᵀ` is the
complex structure of `H¹(X̂, ℝ)` inside `V_ℝ`. -/
def IsAmpleClass (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (Θ : Spinor n) : Prop :=
  Θ ∈ ⋀[ℂ]^2 (H1 n) ∧ IsIntegralClass Θ ∧ HasHodgeType J 1 1 Θ ∧
    ∀ a : Fin (2 * n) → ℝ, a ≠ 0 →
      0 < (formEval Θ (realH1 a) ((-(cMat J).transpose).mulVec (realH1 a))).re

/-- The exponential `exp(s) = ∑_{k ≤ 2n} s^k / k!` in `H^*(X, ℂ)` (for `s ∈ H²(X, ℂ)` all
higher powers vanish). -/
def expS (s : Spinor n) : Spinor n :=
  ∑ k ∈ Finset.range (2 * n + 1), ((k.factorial : ℂ)⁻¹) • s ^ k

/-- The square root `√-d = √d · exp(iπ/2) = i√d` of `-d`, with argument `π/2`. -/
def sqrtNeg (d : ℚ) : ℂ := Complex.I * ((Real.sqrt (d : ℝ) : ℝ) : ℂ)

end MarkmanSecant

end
