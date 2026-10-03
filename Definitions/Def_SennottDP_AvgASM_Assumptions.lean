import Mathlib
import Definitions.Def_SennottDP_AvgASM_ApproxSeq

namespace SennottDP.AvgASM

open scoped ENNReal NNReal Topology
open Filter

variable {S : Type*} {Act : Type*} [Countable S]

namespace ApproxSeq

variable {M : MDC S Act} (AS : ApproxSeq M)

/-- The right-hand side of (8.1) for the action `a` at `i ∈ S_N`:
`C(i, a) + ∑_{j ∈ S_N} P_ij(a; N) r^N(j)`. (`P_ij(a; N) ≤ 1` is finite, so `toReal` is exact.) -/
noncomputable def acoeTerm (rN : ℕ → S → ℝ) (N : ℕ) (i : S) (a : Act) : ℝ :=
  (M.C i a : ℝ) + ∑ j ∈ AS.SN N, (AS.PN N i a j).toReal * rN N j

/-- (AC1), p. 169: the (finite) constants `J^N` and (finite) functions `r^N` on `S_N` satisfy
`J^N + r^N(i) = min_a {C(i, a) + ∑_{j ∈ S_N} P_ij(a; N) r^N(j)}` for `i ∈ S_N`, `N ≥ N₀` (8.1).
(The values `r^N(i)` for `i ∉ S_N` are not constrained.) -/
def AC1 (JN : ℕ → ℝ) (rN : ℕ → S → ℝ) : Prop :=
  ∀ N, AS.N₀ ≤ N → ∀ i ∈ AS.SN N,
    JN N + rN N i = (M.A i).inf' (M.A_nonempty i) (fun a => AS.acoeTerm rN N i a)

/-- (AC2), p. 169: `limsup_{N→∞} r^N(i) < ∞` for `i ∈ S` (computed in `EReal`; `r^N(i)` is
defined for all sufficiently large `N`). -/
def AC2 {M : MDC S Act} (_AS : ApproxSeq M) (rN : ℕ → S → ℝ) : Prop :=
  ∀ i, limsup (fun N => (rN N i : EReal)) atTop < ⊤

/-- (AC3), p. 169: there exists a nonnegative (finite) constant `Q` such that
`−Q ≤ liminf_{N→∞} r^N(i)` for `i ∈ S`. -/
def AC3 {M : MDC S Act} (_AS : ApproxSeq M) (rN : ℕ → S → ℝ) : Prop :=
  ∃ Q : ℝ, 0 ≤ Q ∧ ∀ i, ((-Q : ℝ) : EReal) ≤ liminf (fun N => (rN N i : EReal)) atTop

/-- (AC4), p. 169: `limsup_{N→∞} J^N =: J* < ∞` and `J* ≤ J(i)` for `i ∈ S`, where `J(i)` is the
minimum average cost of `Δ` (in `[0, ∞]`); the comparison is made in `EReal`. -/
def AC4 {M : MDC S Act} (_AS : ApproxSeq M) (JN : ℕ → ℝ) : Prop :=
  limsup (fun N => (JN N : EReal)) atTop < ⊤ ∧
    ∀ i, limsup (fun N => (JN N : EReal)) atTop ≤ ((avgValue M i : ℝ≥0∞) : EReal)

/-- The (AC) assumptions, p. 169, for the witnesses `J^N`, `r^N` of (AC1). -/
def AC (JN : ℕ → ℝ) (rN : ℕ → S → ℝ) : Prop :=
  AS.AC1 JN rN ∧ AS.AC2 rN ∧ AS.AC3 rN ∧ AS.AC4 JN

/-- `u(i) = liminf_{N→∞} r^N(i)`, in `EReal` ((WAC3₁), p. 193). -/
noncomputable def liminfR {M : MDC S Act} (_AS : ApproxSeq M) (rN : ℕ → S → ℝ) (i : S) : EReal :=
  liminf (fun N => (rN N i : EReal)) atTop

/-- `E_e[w(X_n) | X_0 = i]` for the Markov chain induced by the stationary policy `e` of `Δ` and
an extended-real function `w`, as the difference of the expectations of its positive and
negative parts, `∑_j P^{(n)}_{ij}(e) w⁺(j) − ∑_j P^{(n)}_{ij}(e) w⁻(j)`, computed in `EReal`.
It is `> −∞` exactly when the negative part has finite expectation (when both parts are
infinite the `EReal` difference is `−∞`). -/
noncomputable def expectEReal {M : MDC S Act} (_AS : ApproxSeq M) (e : StationaryPolicy M) (w : S → EReal) (n : ℕ) (i : S) : EReal :=
  ((∑' j, nStep e.chain n i j * (w j).toENNReal : ℝ≥0∞) : EReal) -
    ((∑' j, nStep e.chain n i j * (-(w j)).toENNReal : ℝ≥0∞) : EReal)

/-- (WAC3₁), p. 193: there exists a nonnegative (finite) function `Q` on `S` such that
`−Q(i) ≤ liminf_{N→∞} r^N(i) =: u(i)` for `i ∈ S`; and (WAC3₂), pp. 193–194, for that `Q`: for
every stationary policy `e` for `Δ` and initial state `X_0 = i`,
(i) `lim_{N→∞} ∑_{j ∈ S_N} P_ij(e; N) Q(j) = ∑_j P_ij(e) Q(j) < ∞`,
(ii) `−∞ < E_e[u(X_n)]` for `n ≥ 1`,
(iii) `liminf_{n→∞} E_e[u(X_n)]/n ≥ 0`. -/
def WAC3 (rN : ℕ → S → ℝ) : Prop :=
  ∃ Q : S → ℝ≥0,
    (∀ i, ((-(Q i : ℝ) : ℝ) : EReal) ≤ AS.liminfR rN i) ∧
    ∀ e : StationaryPolicy M, ∀ i,
      (Tendsto (fun N => ∑ j ∈ AS.SN N, AS.PN N i (e.f i) j * (Q j : ℝ≥0∞)) atTop
          (𝓝 (∑' j, M.P i (e.f i) j * (Q j : ℝ≥0∞))) ∧
        ∑' j, M.P i (e.f i) j * (Q j : ℝ≥0∞) < ⊤) ∧
      (∀ n, 1 ≤ n → (⊥ : EReal) < AS.expectEReal e (AS.liminfR rN) n i) ∧
      0 ≤ liminf (fun n : ℕ => AS.expectEReal e (AS.liminfR rN) n i / (n : EReal)) atTop

/-- The (WAC) assumptions, pp. 193–194: (WAC1), (WAC2), (WAC4) are (AC1), (AC2), (AC4), and
(WAC3) = (WAC3₁) + (WAC3₂). -/
def WAC (JN : ℕ → ℝ) (rN : ℕ → S → ℝ) : Prop :=
  AS.AC1 JN rN ∧ AS.AC2 rN ∧ AS.WAC3 rN ∧ AS.AC4 JN

/-- The conclusion of Proposition 8.2.1 (pp. 171–172) for the base point `x`: the value iteration
algorithm is justified in each `Δ_N` — the limits `J^N = lim_{n→∞} (v^N_{n+1}(x) − v^N_n(x))` and
`r^N(i) = lim_{n→∞} (v^N_n(i) − v^N_n(x))` (`i ∈ S_N`) exist (the conclusions of Proposition
6.6.3 in `Δ_N`) — and the (AC) assumptions hold for these `J^N` and `r^N`. The finite horizon
values of the finite model `Δ_N` are finite, so `toReal` is exact. -/
def VIAAndAC (x : S) : Prop :=
  ∃ (JN : ℕ → ℝ) (rN : ℕ → S → ℝ),
    (∀ N, AS.N₀ ≤ N → Tendsto (fun n => (AS.valueN (n + 1) N x).toReal - (AS.valueN n N x).toReal)
        atTop (𝓝 (JN N))) ∧
    (∀ N, AS.N₀ ≤ N → ∀ i ∈ AS.SN N,
      Tendsto (fun n => (AS.valueN n N i).toReal - (AS.valueN n N x).toReal) atTop
        (𝓝 (rN N i))) ∧
    AS.AC JN rN

end ApproxSeq

end SennottDP.AvgASM
