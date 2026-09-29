import Mathlib

namespace MonotoneDP.Decrease

open Filter Topology

/-- The abstract dynamic programming model of Bertsekas (1977), Sections 2–3 (pp. 441–442).

* `S`, `C` are the state and control spaces; `S` is nonempty (Section 2, item 1), and `C` is
  nonempty because every `U x` is.
* `U x ⊆ C` is the nonempty control constraint set at `x` (item 2).
* `H : S → C → (S → EReal) → EReal` is the given mapping `H : S × C × F → [−∞, +∞]` (item 7),
  where `F = S → EReal` is the set of extended-real-valued functions on `S` (item 4).
* `mono` is the Monotonicity assumption, in effect throughout the paper (p. 441).
* `Jbar` is the given terminal function `J̄ ∈ F` with `J̄(x) > −∞` for all `x` (Section 3). -/
structure Model (S C : Type*) where
  S_nonempty : Nonempty S
  U : S → Set C
  U_nonempty : ∀ x, (U x).Nonempty
  H : S → C → (S → EReal) → EReal
  mono : ∀ x, ∀ u ∈ U x, ∀ J J' : S → EReal, J ≤ J' → H x u J ≤ H x u J'
  Jbar : S → EReal
  Jbar_ne_bot : ∀ x, Jbar x ≠ ⊥

namespace Model

variable {S C : Type*} (m : Model S C)

/-- The set `M` of admissible selectors: functions `μ : S → C` with `μ(x) ∈ U(x)` for all `x`. -/
def Selector : Type _ := {μ : S → C // ∀ x, μ x ∈ m.U x}

/-- The set `Π` of policies: sequences `π = {μ₀, μ₁, …}` of admissible selectors. -/
def Policy : Type _ := ℕ → m.Selector

/-- The stationary policy `{μ, μ, …}`. -/
def stationary (μ : m.Selector) : m.Policy := fun _ => μ

/-- `T_μ(J)(x) = H(x, μ(x), J)`, eq. (15). -/
def Tmu (μ : m.Selector) (J : S → EReal) : S → EReal := fun x => m.H x (μ.1 x) J

/-- `T(J)(x) = inf_{u ∈ U(x)} H(x, u, J)`, eq. (16). `T^k` is `m.T^[k]`, with `T^0 = id`. -/
noncomputable def T (J : S → EReal) : S → EReal := fun x => ⨅ u ∈ m.U x, m.H x u J

/-- The composition `(T_{μ₀} T_{μ₁} ⋯ T_{μ_{N−1}})(J)`: `T_{μ_{N−1}}` is applied to `J` first and
`T_{μ₀}` last; `comp π 0 J = J`. -/
def comp (π : m.Policy) : ℕ → (S → EReal) → (S → EReal)
  | 0, J => J
  | N + 1, J => comp π N (m.Tmu (π N) J)

/-- The value function of a policy, eq. (17):
`J_π(x) = lim_{N → ∞} (T_{μ₀} ⋯ T_{μ_{N−1}})(J̄)(x)`, as `limUnder`. Under Assumption D the
sequence is nonincreasing in `N` (eq. (25)), so the limit exists in `[−∞, ∞]`; every result
about `J_π` is stated under Assumption D. -/
noncomputable def Jpi (π : m.Policy) : S → EReal :=
  fun x => limUnder atTop (fun N => m.comp π N m.Jbar x)

/-- `J_μ`, the value function of the stationary policy `{μ, μ, …}`. -/
noncomputable def Jmu (μ : m.Selector) : S → EReal := m.Jpi (m.stationary μ)

/-- The optimal value function, eq. (19): `J*(x) = inf_{π ∈ Π} J_π(x)`. -/
noncomputable def Jstar : S → EReal := fun x => ⨅ π : m.Policy, m.Jpi π x

/-- The optimal value function of the `N`-stage problem, eq. (36):
`J_N(x) = inf_{π ∈ Π} (T_{μ₀} ⋯ T_{μ_{N−1}})(J̄)(x)`. The paper uses it for `N ≥ 1`; for `N = 0`
the formula gives `J̄`. -/
noncomputable def JN (N : ℕ) : S → EReal := fun x => ⨅ π : m.Policy, m.comp π N m.Jbar x

/-- The limit of the DP algorithm, eq. (49): `J_∞(x) = lim_{N → ∞} T^N(J̄)(x)`, as `limUnder`.
Under Assumption D the sequence `T^N(J̄)(x)` is nonincreasing, so the limit exists. -/
noncomputable def Jinf : S → EReal := fun x => limUnder atTop (fun N => (m.T)^[N] m.Jbar x)

end Model

end MonotoneDP.Decrease
