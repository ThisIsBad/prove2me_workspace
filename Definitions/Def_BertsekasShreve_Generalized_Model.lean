import Mathlib
import Definitions.Def_BertsekasShreve_Contraction_Model

namespace BertsekasShreve.Generalized

open Filter Topology

/-- The generalized abstract dynamic programming model of Bertsekas & Shreve, Section 6.1
(pp. 92–93), built on the notation of Section 2.1 (pp. 26–27).

* `S`, `C` are the state and control spaces (item (1), p. 26).
* `U x ⊆ C` is the nonempty control constraint set at `x` (item (2), p. 26).
* `Fstar` and `Ftil` are the two given subsets `F* ⊂ F̃ ⊂ F` of the set `F = S → EReal` of
  extended-real-valued functions on `S` (p. 92). They are arbitrary sets; only the conditions
  A.1–A.5 (stated separately) constrain them.
* `Mtil` is the given subset `M̃` of the set `M` of functions `μ : S → C` with `μ(x) ∈ U(x)` for
  all `x` (p. 92).
* `H : S → C → (S → EReal) → EReal` is the mapping `H : S C F̃ → R*` of p. 92. Lean's `H` is total,
  but the book defines it on `S × C × F̃` only: `mono`, the monotonicity assumption of p. 92, is
  required only for `u ∈ U(x)` and `J, J' ∈ F̃`, and every statement of the mission evaluates `H`
  only at functions that lie in `F̃`.
* `J0` is the given function `J₀ ∈ F*` with `J₀(x) > −∞` for all `x` (p. 92). -/
structure Model (S C : Type*) where
  U : S → Set C
  U_nonempty : ∀ x, (U x).Nonempty
  Fstar : Set (S → EReal)
  Ftil : Set (S → EReal)
  Fstar_subset : Fstar ⊆ Ftil
  Mtil : Set (S → C)
  Mtil_subset : ∀ μ ∈ Mtil, ∀ x, μ x ∈ U x
  H : S → C → (S → EReal) → EReal
  mono : ∀ x, ∀ u ∈ U x, ∀ J ∈ Ftil, ∀ J' ∈ Ftil, J ≤ J' → H x u J ≤ H x u J'
  J0 : S → EReal
  J0_mem : J0 ∈ Fstar
  J0_ne_bot : ∀ x, J0 x ≠ ⊥

namespace Model

variable {S C : Type*} (P : Model S C)

/-- An element of `M̃`. -/
def Sel : Type _ := {μ : S → C // μ ∈ P.Mtil}

/-- The set `Π̃ = {(μ₀, μ₁, …) ∈ Π | μ_k ∈ M̃, k = 0, 1, …}` of policies built from `M̃` (p. 92). -/
def Policy : Type _ := ℕ → P.Sel

/-- The stationary policy `(μ, μ, …) ∈ Π̃`. -/
def stationary (μ : P.Sel) : P.Policy := fun _ => μ

/-- The tail `(μ_i, μ_{i+1}, …)` of a policy `π = (μ₀, μ₁, …)`. -/
def shift (π : P.Policy) (i : ℕ) : P.Policy := fun k => π (i + k)

/-- `T_μ(J)(x) = H[x, μ(x), J]` (p. 92). -/
def Tmu (μ : S → C) (J : S → EReal) : S → EReal := fun x => P.H x (μ x) J

/-- `T(J)(x) = inf_{u ∈ U(x)} H(x, u, J)` (p. 92). `T^k` is `P.T^[k]`, with `T^0 = id`. -/
noncomputable def T (J : S → EReal) : S → EReal := fun x => ⨅ u ∈ P.U x, P.H x u J

/-- The composition `(T_{μ₀} T_{μ₁} ⋯ T_{μ_{N−1}})(J)`: `T_{μ_{N−1}}` is applied to `J` first and
`T_{μ₀}` last; `comp π 0 J = J` (p. 27). -/
def comp (π : P.Policy) : ℕ → (S → EReal) → (S → EReal)
  | 0, J => J
  | N + 1, J => comp π N (P.Tmu (π N).1 J)

/-- The `N`-stage cost function `J_{N,π}(x) = (T_{μ₀} ⋯ T_{μ_{N−1}})(J₀)(x)`, eq. (1) of Chapter 6. -/
def JN (N : ℕ) (π : P.Policy) : S → EReal := P.comp π N P.J0

/-- The cost function `J_π(x) = lim_{N → ∞} (T_{μ₀} ⋯ T_{μ_{N−1}})(J₀)(x)`, eq. (2) of Chapter 6,
taken as `limUnder`; it is the true limit whenever the limit exists in `[−∞, ∞]` (under
Assumption C̃ it exists and is real). -/
noncomputable def Jpi (π : P.Policy) : S → EReal :=
  fun x => limUnder atTop (fun N => P.comp π N P.J0 x)

/-- `J_μ = J_π` for the stationary policy `π = (μ, μ, …)` (p. 29). -/
noncomputable def Jmu (μ : P.Sel) : S → EReal := P.Jpi (P.stationary μ)

/-- `J*_N(x) = inf_{π ∈ Π̃} J_{N,π}(x)` (p. 93). The infimum is over `Π̃` only. -/
noncomputable def JNstar (N : ℕ) : S → EReal := fun x => ⨅ π : P.Policy, P.JN N π x

/-- `J*(x) = inf_{π ∈ Π̃} J_π(x)` (p. 93). The infimum is over `Π̃` only. -/
noncomputable def Jstar : S → EReal := fun x => ⨅ π : P.Policy, P.Jpi π x

end Model

/-- `J ∈ B̄ ∩ G` for a set `B̄ ⊆ B` and a set `G ⊆ F` (used with `G = F*` and `G = F̃`): `J` is a
bounded real function lying in `B̄`, viewed as an element of `F`, and it belongs to `G`. -/
def MemBbarInter {S : Type*} (Bbar : Set (BertsekasShreve.Contraction.BFun S)) (G : Set (S → EReal)) (J : S → EReal) : Prop :=
  ∃ J' ∈ Bbar, J = BertsekasShreve.Contraction.toF J' ∧ J ∈ G

/-- The function `J + r`, `(J + r)(x) = J(x) + r`, for a real scalar `r` (item (5), p. 26). -/
noncomputable def addConst {S : Type*} (J : S → EReal) (r : ℝ) : S → EReal :=
  fun x => J x + (r : EReal)

end BertsekasShreve.Generalized
