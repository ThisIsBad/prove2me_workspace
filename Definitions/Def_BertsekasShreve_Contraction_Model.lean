import Mathlib

namespace BertsekasShreve.Contraction

open Filter Topology

/-- The abstract monotone dynamic programming model of Bertsekas & Shreve, Sections 2.1–2.2
(pp. 26–28).

* `S`, `C` are the state and control spaces (item (1), p. 26).
* `U x ⊆ C` is the nonempty control constraint set at `x` (item (2)).
* `H : S → C → (S → EReal) → EReal` is the basic mapping `H : SCF → R*` (p. 27), where
  `F = S → EReal` is the set of extended-real-valued functions on `S` (item (4)).
* `mono` is the Monotonicity Assumption (3), p. 27, in effect throughout Part I.
* `J0` is the given function `J₀ ∈ F` with `J₀(x) > −∞` for all `x` (eq. (4), p. 28). -/
structure Model (S C : Type*) where
  U : S → Set C
  U_nonempty : ∀ x, (U x).Nonempty
  H : S → C → (S → EReal) → EReal
  mono : ∀ x, ∀ u ∈ U x, ∀ J J' : S → EReal, J ≤ J' → H x u J ≤ H x u J'
  J0 : S → EReal
  J0_ne_bot : ∀ x, J0 x ≠ ⊥

namespace Model

variable {S C : Type*} (P : Model S C)

/-- The set `M` of functions `μ : S → C` with `μ(x) ∈ U(x)` for all `x` (item (3), p. 26). -/
def Selector : Type _ := {μ : S → C // ∀ x, μ x ∈ P.U x}

/-- The set `Π` of policies `π = (μ₀, μ₁, …)` with every `μ_k ∈ M` (item (3), p. 26). -/
def Policy : Type _ := ℕ → P.Selector

/-- The stationary policy `(μ, μ, …)`. -/
def stationary (μ : P.Selector) : P.Policy := fun _ => μ

/-- `T_μ(J)(x) = H[x, μ(x), J]`, eq. (1) of Chapter 2. -/
def Tmu (μ : P.Selector) (J : S → EReal) : S → EReal := fun x => P.H x (μ.1 x) J

/-- `T(J)(x) = inf_{u ∈ U(x)} H(x, u, J)`, eq. (2) of Chapter 2. `T^k` is `P.T^[k]`, `T^0 = id`. -/
noncomputable def T (J : S → EReal) : S → EReal := fun x => ⨅ u ∈ P.U x, P.H x u J

/-- The composition `(T_{μ₀} T_{μ₁} ⋯ T_{μ_{N−1}})(J)`: `T_{μ_{N−1}}` is applied to `J` first and
`T_{μ₀}` last; `comp π 0 J = J`. -/
def comp (π : P.Policy) : ℕ → (S → EReal) → (S → EReal)
  | 0, J => J
  | N + 1, J => comp π N (P.Tmu (π N) J)

/-- The cost function of a policy, eq. (6) of Chapter 2:
`J_π(x) = lim_{N → ∞} (T_{μ₀} ⋯ T_{μ_{N−1}})(J₀)(x)`, taken as `limUnder`; it is the true limit
whenever the limit exists (under Assumption C it exists and is real). -/
noncomputable def Jpi (π : P.Policy) : S → EReal :=
  fun x => limUnder atTop (fun N => P.comp π N P.J0 x)

/-- `J_μ = J_π` for the stationary policy `π = (μ, μ, …)` (p. 29). -/
noncomputable def Jmu (μ : P.Selector) : S → EReal := P.Jpi (P.stationary μ)

/-- The optimal cost function, eq. (8) of Chapter 2: `J*(x) = inf_{π ∈ Π} J_π(x)`. -/
noncomputable def Jstar : S → EReal := fun x => ⨅ π : P.Policy, P.Jpi π x

/-- The `N`-stage optimal cost function, eq. (7) of Chapter 2:
`J*_N(x) = inf_{π ∈ Π} (T_{μ₀} ⋯ T_{μ_{N−1}})(J₀)(x)`. -/
noncomputable def JNstar (N : ℕ) : S → EReal := fun x => ⨅ π : P.Policy, P.comp π N P.J0 x

end Model

/-- The Banach space `B` of bounded real-valued functions on `S` with the supremum norm
`‖J‖ = sup_{x ∈ S} |J(x)|` (item (4), p. 26), as Mathlib's `ℓ^∞(S, ℝ)`. -/
abbrev BFun (S : Type*) := lp (fun _ : S => ℝ) ⊤

/-- A bounded real function viewed as an element of `F = S → EReal`. -/
def toF {S : Type*} (J : BFun S) : S → EReal := fun x => ((J x : ℝ) : EReal)

/-- `‖J − J'‖ ≤ c` for extended-real-valued functions, read with the book's arithmetic
(`∞ − ∞ = −∞ + ∞ = ∞`, p. 26): `J(x)` and `J'(x)` are real at every `x` and
`|J(x) − J'(x)| ≤ c`. Under the book's conventions any infinite value makes the difference
`±∞` at that point, so the sup-norm bound forces finiteness. -/
def SupDistLe {S : Type*} (J J' : S → EReal) (c : ℝ) : Prop :=
  ∀ x, ∃ a b : ℝ, J x = (a : EReal) ∧ J' x = (b : EReal) ∧ |a - b| ≤ c

end BertsekasShreve.Contraction
