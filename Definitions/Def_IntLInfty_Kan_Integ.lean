import Mathlib
import Definitions.Def_IntLInfty_Kan_CE
import Definitions.Def_IntLInfty_Kan_Forms
import Definitions.Def_IntLInfty_Kan_Manifold

namespace IntLInfty.Kan

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

theorem gen_mem_genAlg (S : GenSys L) {i : ℕ} {ξ : Module.Dual ℝ (L i)} (h : ξ ∈ S i) :
    gen L i ξ ∈ genAlg L S :=
  Algebra.subset_adjoin (Set.mem_iUnion.2 ⟨i, ξ, h, rfl⟩)

/-- `φ : A_S → Ω∗(Δᵐ)` is a homomorphism of differential graded algebras into `Ω∗_{Cʳ}(Δᵐ)`:
a generator from `L∗ᵢ` goes to an `(i+1)`-form, every value is a `Cʳ` form with `Cʳ` exterior
derivative, and `d ∘ φ = φ ∘ δ` on `Δᵐ`. -/
def IsDGAMap (r : ℕ) (δ : LInfty L) (S : GenSys L) (m : ℕ) (φ : genAlg L S →ₐ[ℝ] Ω m) : Prop :=
  (∀ (i : ℕ) (ξ : Module.Dual ℝ (L i)) (h : ξ ∈ S i), IsDeg (i + 1) (φ ⟨gen L i ξ, gen_mem_genAlg S h⟩)) ∧
  (∀ a, IsCr r (φ a)) ∧
  (∀ a b : genAlg L S, δ.δ a = b → ∀ x ∈ simplex m, extD (φ a) x = φ b x)

variable [∀ i, FiniteDimensional ℝ (L i)]

/-- The chosen basis of the generator space `S i`. -/
noncomputable def genBasis (S : GenSys L) (i : ℕ) :
    Module.Basis (Fin (Module.finrank ℝ (S i))) ℝ (S i) :=
  haveI := Module.Free.of_divisionRing ℝ (S i)
  Module.finBasis ℝ (S i)

/-- The ambient Banach space of `(∫_S)ₘ`: the images of the basis generators of `S i`, `i < m`,
in `Ω^{i+1}_{Cʳ}(Δᵐ)` (generators of degree `> m` go to `0`). -/
def Amb (r : ℕ) (S : GenSys L) (m : ℕ) : Type :=
  (t : Fin m) → (Fin (Module.finrank ℝ (S t)) → CrForms r m (t + 1))

noncomputable instance (r : ℕ) (S : GenSys L) (m : ℕ) : NormedAddCommGroup (Amb r S m) :=
  inferInstanceAs (NormedAddCommGroup ((t : Fin m) → (Fin (Module.finrank ℝ (S t)) → CrForms r m (t + 1))))

noncomputable instance (r : ℕ) (S : GenSys L) (m : ℕ) : NormedSpace ℝ (Amb r S m) :=
  inferInstanceAs (NormedSpace ℝ ((t : Fin m) → (Fin (Module.finrank ℝ (S t)) → CrForms r m (t + 1))))

/-- `(∫_S)ₘ = Hom_DGA(A_S, Ω∗(Δᵐ))` (Definition 5.2), as the subset of `Amb r S m` of the generator
images of the DGA maps. `∫_⊤ = ∫L`; `∫_{tauLe δ n} = ∫τ≤ₙL`; `∫_{tauLt δ n} = ∫τ<ₙL`; `∫_⊥ = ∗`. -/
def integ (r : ℕ) (δ : LInfty L) (S : GenSys L) (m : ℕ) : Set (Amb r S m) :=
  {z | ∃ φ : genAlg L S →ₐ[ℝ] Ω m, IsDGAMap r δ S m φ ∧
    ∀ (t : Fin m) (k : Fin (Module.finrank ℝ (S t))),
      (z t k : Jet r m × Jet r m) = jet r (φ ⟨gen L t (genBasis S t k), gen_mem_genAlg S (genBasis S t k).2⟩)}

/-- The face map `dᵢ : Amb r S (m+1) → Amb r S m`: pull back every coordinate along the `i`-th
coface and drop the generators of degree `m + 1`. -/
noncomputable def faceAmb (r : ℕ) (S : GenSys L) (m : ℕ) (i : Fin (m + 2)) (z : Amb r S (m + 1)) :
    Amb r S m :=
  fun t k => faceCr r m (t + 1) i (z t.castSucc k)

/-- For `S' ≤ S`, the map `∫_S → ∫_{S'}` induced by `A_{S'} ⊆ A_S`: restrict every coordinate to
`S' i ⊆ S i`. -/
noncomputable def res {S S' : GenSys L} (h : ∀ i, S' i ≤ S i) {r m : ℕ} (z : Amb r S m) : Amb r S' m :=
  fun t k => ∑ l, (genBasis S t).repr (Submodule.inclusion (h t) (genBasis S' t k)) l • z t l

/-- The object of commutative squares (10), `Hom(Λ[m+1, j] → Δ[m+1], ∫_S → ∫_{S'})`: a compatible
tuple `(xᵢ)_{i ≠ j}` of points of `(∫_S)ₘ` and a point `y` of `(∫_{S'})_{m+1}` with `dᵢ y = res xᵢ`. -/
def RelHorn (r : ℕ) (δ : LInfty L) {S S' : GenSys L} (h : ∀ i, S' i ≤ S i) (m : ℕ) (j : Fin (m + 2)) :
    Set (({i : Fin (m + 2) // i ≠ j} → Amb r S m) × Amb r S' (m + 1)) :=
  {p | (∀ i, p.1 i ∈ integ r δ S m) ∧ p.2 ∈ integ r δ S' (m + 1) ∧
    HornCompat (fun q => faceAmb r S q) m j p.1 ∧ ∀ i, faceAmb r S' m i.1 p.2 = res h (p.1 i)}

/-- The map `(∫_S)_{m+1} → Hom(Λ[m+1, j] → Δ[m+1], ∫_S → ∫_{S'})`, `z ↦ ((dᵢ z)_{i ≠ j}, res z)`. -/
noncomputable def kanMap {r : ℕ} {S S' : GenSys L} (h : ∀ i, S' i ≤ S i) (m : ℕ) (j : Fin (m + 2))
    (z : Amb r S (m + 1)) : ({i : Fin (m + 2) // i ≠ j} → Amb r S m) × Amb r S' (m + 1) :=
  (fun i => faceAmb r S m i.1 z, res h z)

/-- `∫_S → ∫_{S'}` is a Kan fibration (Definition 2.3, covers = surjective submersions): `S' ≤ S`,
every `(∫_S)ₘ` and `(∫_{S'})ₘ` is a `C^∞` split submanifold of its ambient space, and for all
`m ≥ 1`, `0 ≤ j ≤ m`, the object of squares (10) is a `C^∞` split submanifold and the map from
`(∫_S)ₘ` to it is a surjective submersion. With `S' = ⊥` this is the Kan condition (4). -/
def IsKanFibration (r : ℕ) (δ : LInfty L) (S S' : GenSys L) : Prop :=
  ∃ h : ∀ i, S' i ≤ S i,
    (∀ m, IsSplitSubmanifold (integ r δ S m)) ∧ (∀ m, IsSplitSubmanifold (integ r δ S' m)) ∧
    ∀ (m : ℕ) (j : Fin (m + 2)), IsSplitSubmanifold (RelHorn r δ h m j) ∧
      IsSurjSubmersionOn (kanMap h m j) (integ r δ S (m + 1)) (RelHorn r δ h m j)

end IntLInfty.Kan
