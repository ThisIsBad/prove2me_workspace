import Mathlib
import Definitions.Def_MonotonicSolutions_StrongMono_Game

namespace MonotonicSolutions.StrongMono

/-- Strong monotonicity, Eq. (6) of Young (1985, p. 69): for all games `v, w` and every player
`i`, if `w^i(S) ≤ v^i(S)` for every coalition `S`, then `φ_i(w) ≤ φ_i(v)`. -/
def IsStronglyMonotonic {n : ℕ} (φ : Game n → Fin n → ℝ) : Prop :=
  ∀ (v w : Game n) (i : Fin n),
    (∀ S : Finset (Fin n), marginal w.1 i S ≤ marginal v.1 i S) → φ w i ≤ φ v i

/-- Marginality (independence), Eq. (7) of Young (1985, p. 70): a player's allocation depends
only on the vector of his marginal contributions; if `v^i(S) = w^i(S)` for every coalition `S`,
then `φ_i(v) = φ_i(w)`. -/
def IsMarginal {n : ℕ} (φ : Game n → Fin n → ℝ) : Prop :=
  ∀ (v w : Game n) (i : Fin n),
    (∀ S : Finset (Fin n), marginal v.1 i S = marginal w.1 i S) → φ v i = φ w i

/-- The permuted game `πv` (Young 1985, p. 69), in the standard reading `(πv)(πS) = v(S)`,
i.e. `(πv)(T) = v(π⁻¹ T)`: the coalition `π S` plays in `πv` the role `S` plays in `v`. -/
def permGame {n : ℕ} (π : Equiv.Perm (Fin n)) (v : Game n) : Game n :=
  ⟨fun T => v.1 (T.map π.symm.toEmbedding), by simpa using v.2⟩

/-- Symmetry (Young 1985, p. 69): for every permutation `π` of `N`, every game `v` and every
player `i`, `φ_{π i}(πv) = φ_i(v)`, where `(πv)(πS) = v(S)`. -/
def IsSymmetric {n : ℕ} (φ : Game n → Fin n → ℝ) : Prop :=
  ∀ (π : Equiv.Perm (Fin n)) (v : Game n) (i : Fin n), φ (permGame π v) (π i) = φ v i

/-- Shapley's dummy axiom, Eq. (11) of Young (1985, p. 71): if `v^i(S) = 0` for every
coalition `S`, then `φ_i(v) = 0`. -/
def SatisfiesDummy {n : ℕ} (φ : Game n → Fin n → ℝ) : Prop :=
  ∀ (v : Game n) (i : Fin n), (∀ S : Finset (Fin n), marginal v.1 i S = 0) → φ v i = 0

/-- The sum `v + w` of two games, `(v + w)(S) = v(S) + w(S)`; it vanishes at `∅`. -/
def addGame {n : ℕ} (v w : Game n) : Game n :=
  ⟨fun S => v.1 S + w.1 S, by simp [v.2, w.2]⟩

/-- Shapley's additivity axiom (Young 1985, p. 71): `φ(v + w) = φ(v) + φ(w)` for all games
`v, w`. -/
def IsAdditive {n : ℕ} (φ : Game n → Fin n → ℝ) : Prop :=
  ∀ v w : Game n, φ (addGame v w) = φ v + φ w

end MonotonicSolutions.StrongMono
