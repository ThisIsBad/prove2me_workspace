import Mathlib

namespace AppliedComb.Polya

open MvPolynomial

/-- Keller–Trotter, Sections 15.1 and 15.3 (pp. 294, 297–298). The colorings of `S` with the `m`
colors `c_1, …, c_m` are the maps `f : S → Fin m` (color index `i : Fin m` stands for
`c_{i+1}`). A permutation `π` of `S` acts on colorings by `π^*(f) = f ∘ π⁻¹` (the color that `f`
puts at `s` is carried to `π(s)`), and two colorings are equivalent, `f ∼ f'`, when
`π^*(f) = f'` for some `π ∈ G`. This is the equivalence relation on colorings induced by the
permutation group `G` (a subgroup of `Equiv.Perm S`). -/
def colorSetoid {S : Type*} (G : Subgroup (Equiv.Perm S)) (m : ℕ) : Setoid (S → Fin m) where
  r f f' := ∃ π ∈ G, f' = f ∘ ⇑π⁻¹
  iseqv := by
    refine ⟨fun f => ⟨1, G.one_mem, by simp⟩, ?_, ?_⟩
    · rintro f f' ⟨π, hπ, rfl⟩
      refine ⟨π⁻¹, G.inv_mem hπ, ?_⟩
      funext s
      simp
    · rintro f f' f'' ⟨π, hπ, rfl⟩ ⟨τ, hτ, rfl⟩
      refine ⟨τ * π, G.mul_mem hτ hπ, ?_⟩
      funext s
      simp [mul_inv_rev]

/-- The weight of a coloring `f : S → Fin m`: the monomial `c_1^{a_1} ⋯ c_m^{a_m}` in commuting
variables `c_1, …, c_m`, where `a_i` is the number of elements of `S` that `f` colors `c_i`. It
is written as the product over `s ∈ S` of the variable of the color of `s`. -/
noncomputable def colorWeight {S : Type*} [Fintype S] {m : ℕ} (f : S → Fin m) :
    MvPolynomial (Fin m) ℚ :=
  ∏ s : S, X (f s)

open Classical in
/-- Keller–Trotter, Section 15.4.2 (pp. 301–303). The generating function for the number of
nonequivalent colorings of `S` (the *pattern inventory*): the polynomial in the colors
`c_1, …, c_m` whose coefficient of `c_1^{a_1} ⋯ c_m^{a_m}` is the number of equivalence classes
of colorings (under the relation `colorSetoid G m` induced by `G`) that use color `c_i` exactly
`a_i` times. It is the sum, over the equivalence classes, of the weight of a representative
(`Quotient.out`) of the class. -/
noncomputable def patternInventory {S : Type*} [Fintype S] (G : Subgroup (Equiv.Perm S))
    (m : ℕ) : MvPolynomial (Fin m) ℚ :=
  ∑ q : Quotient (colorSetoid G m), colorWeight q.out

end AppliedComb.Polya
