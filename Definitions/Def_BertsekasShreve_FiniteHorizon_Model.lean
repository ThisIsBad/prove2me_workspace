import Mathlib

namespace BertsekasShreve.FiniteHorizon

/-- The abstract monotone model of Bertsekas & Shreve, *Stochastic Optimal Control: The
Discrete-Time Case*, Section 2.1, items (1)–(4) and the Monotonicity Assumption (pp. 26–27).

* `S`, `C` are the state space and the control space (item (1)); no nonemptiness is assumed.
* `U x ⊆ C` is the nonempty control constraint set at `x` (item (2)).
* `F = S → EReal` is the set of extended-real-valued functions on `S` (item (4)), ordered
  pointwise (item (5)).
* `H : S × C × F → R*` is the basic mapping (p. 27), curried.
* `mono` is the Monotonicity Assumption, eq. (3) of Chapter 2: for every `x ∈ S`, `u ∈ U(x)`,
  `J ≤ J'` implies `H(x, u, J) ≤ H(x, u, J')`. -/
structure Model (S C : Type*) where
  U : S → Set C
  U_nonempty : ∀ x, (U x).Nonempty
  H : S → C → (S → EReal) → EReal
  mono : ∀ x, ∀ u ∈ U x, ∀ J J' : S → EReal, J ≤ J' → H x u J ≤ H x u J'

namespace Model

variable {S C : Type*} (m : Model S C)

/-- The set `M` of all functions `μ : S → C` with `μ(x) ∈ U(x)` for all `x ∈ S` (item (3)). -/
def Selector : Type _ := {μ : S → C // ∀ x, μ x ∈ m.U x}

/-- The set `Π` of policies: sequences `π = (μ₀, μ₁, …)` with every `μ_k ∈ M` (item (3)). -/
def Policy : Type _ := ℕ → m.Selector

/-- The stationary policy `(μ, μ, …)` (item (3)). -/
def stationary (μ : m.Selector) : m.Policy := fun _ => μ

/-- The tail policy `(μ_i, μ_{i+1}, …)` of `π = (μ₀, μ₁, …)`. -/
def Policy.shift {m : Model S C} (π : m.Policy) (i : ℕ) : m.Policy := fun k => π (i + k)

/-- `T_μ(J)(x) = H[x, μ(x), J]`, eq. (1) of Chapter 2. -/
def Tmu (μ : m.Selector) (J : S → EReal) : S → EReal := fun x => m.H x (μ.1 x) J

/-- `T(J)(x) = inf_{u ∈ U(x)} H(x, u, J)`, eq. (2) of Chapter 2. Its `k`-fold composition
`T^k` is `m.T^[k]`, with `T^0(J) = J`. -/
noncomputable def T (J : S → EReal) : S → EReal := fun x => ⨅ u ∈ m.U x, m.H x u J

/-- The composition `(T_{μ₀} T_{μ₁} ⋯ T_{μ_{N−1}})(J)` for `π = (μ₀, μ₁, …)`: the mapping
`T_{μ_{N−1}}` is applied to `J` first and `T_{μ₀}` last; for `N = 0` it is `J`. -/
def comp (π : m.Policy) : ℕ → (S → EReal) → (S → EReal)
  | 0, J => J
  | N + 1, J => comp π N (m.Tmu (π N) J)

end Model

end BertsekasShreve.FiniteHorizon
