import Mathlib
import Definitions.Def_SennottDP_ContinuousTime_MDC

open scoped ENNReal NNReal
open Classical Filter Topology

namespace SennottDP.ContinuousTime

variable {S Act : Type}

/-- An approximating sequence (AS) `(Δ_N)_{N ≥ N₀}` for the MDC `M` (Definition 2.5.1, p. 28):
an increasing sequence `(S_N)_{N ≥ N₀}` of finite nonempty subsets of `S` with union `S`, and for
each `N ≥ N₀`, `i ∈ S_N`, `a ∈ A i` a probability distribution `P_{i·}(a; N)` on `S_N` with
`lim_{N→∞} P_{ij}(a; N) = P_{ij}(a)` for every `j ∈ S` (2.17). The action sets and costs of
`Δ_N` are those of `M`. The fields `SN N`, `PN N` for `N < N₀`, and `PN N i a j` for `i ∉ S_N`
or `j ∉ S_N`, carry no meaning and enter no statement except through limits in `N`. -/
structure ApproxSeq (M : MDC S Act) where
  N0 : ℕ
  SN : ℕ → Finset S
  SN_nonempty : ∀ N, N0 ≤ N → (SN N).Nonempty
  SN_mono : ∀ N N', N0 ≤ N → N ≤ N' → SN N ⊆ SN N'
  SN_cover : ∀ i, ∃ N, N0 ≤ N ∧ i ∈ SN N
  PN : ℕ → S → Act → S → ℝ≥0∞
  PN_sum : ∀ N, N0 ≤ N → ∀ i ∈ SN N, ∀ a ∈ M.A i, ∑ j ∈ SN N, PN N i a j = 1
  PN_lim : ∀ i, ∀ a ∈ M.A i, ∀ j, Tendsto (fun N => PN N i a j) atTop (𝓝 (M.P i a j))

namespace ApproxSeq

variable {M : MDC S Act} (Δs : ApproxSeq M)

/-- The bracket of the optimality equation (8.1) of `Δ_N` at the action `a`:
`C(i,a) + Σ_{j ∈ S_N} P_{ij}(a; N) r(j)`. -/
noncomputable def bracket (N : ℕ) (r : S → ℝ) (i : S) (a : Act) : ℝ :=
  M.C i a + ∑ j ∈ Δs.SN N, (Δs.PN N i a j).toReal * r j

/-- The (AC) assumptions (p. 169) for the AS `(Δ_N)` with the constants `J^N` (`JN N`) and the
functions `r^N` (`rN N`, meaningful on `S_N`):

* (AC1) for `N ≥ N₀` and `i ∈ S_N`,
  `J^N + r^N(i) = min_{a ∈ A_i} { C(i,a) + Σ_{j ∈ S_N} P_{ij}(a;N) r^N(j) }` (8.1);
* (AC2) `limsup_{N→∞} r^N(i) < ∞` for `i ∈ S`;
* (AC3) there is a finite constant `Q ≥ 0` with `-Q ≤ liminf_{N→∞} r^N(i)` for `i ∈ S`;
* (AC4) `J* := limsup_{N→∞} J^N < ∞` and `J* ≤ J(i)` for `i ∈ S`, `J` the minimum average cost
  of `M`.

The limits superior and inferior are taken in `EReal`, so that `±∞` are the book's values; for
a fixed `i`, `i ∈ S_N` for all large `N`, so the values of `r^N(i)` at `i ∉ S_N` do not matter. -/
def AC (JN : ℕ → ℝ) (rN : ℕ → S → ℝ) : Prop :=
  (∀ N, Δs.N0 ≤ N → ∀ i ∈ Δs.SN N, ∃ hA : (M.A i).Nonempty,
      JN N + rN N i = (M.A i).inf' hA (fun a => Δs.bracket N (rN N) i a)) ∧
    (∀ i, limsup (fun N => ((rN N i : ℝ) : EReal)) atTop < ⊤) ∧
    (∃ Q : ℝ, 0 ≤ Q ∧ ∀ i, ((-Q : ℝ) : EReal) ≤ liminf (fun N => ((rN N i : ℝ) : EReal)) atTop) ∧
    limsup (fun N => ((JN N : ℝ) : EReal)) atTop < ⊤ ∧
    ∀ i, limsup (fun N => ((JN N : ℝ) : EReal)) atTop ≤ ((M.avgValue i : ℝ≥0∞) : EReal)

/-- `eN` is a sequence of stationary policies realizing the minimum in (8.1): for `N ≥ N₀` and
`i ∈ S_N`, `e^N(i) ∈ A_i` attains the minimum of the bracket. -/
def RealizesMin (JN : ℕ → ℝ) (rN : ℕ → S → ℝ) (eN : ℕ → S → Act) : Prop :=
  ∀ N, Δs.N0 ≤ N → ∀ i ∈ Δs.SN N,
    eN N i ∈ M.A i ∧ JN N + rN N i = Δs.bracket N (rN N) i (eN N i)

/-- Definition B.4 (p. 290): the stationary policy `e` of `M` is a limit point of the sequence
`(e^N)_{N ≥ N₀}` of stationary policies of the `Δ_N` if there is a subsequence `N_r ≥ N₀` such
that for each `i ∈ S`, `e^{N_r}(i) = e(i)` for all large `r`. -/
def IsLimitPoint (eN : ℕ → S → Act) (e : S → Act) : Prop :=
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ r, Δs.N0 ≤ φ r) ∧ ∀ i, ∀ᶠ r in atTop, eN (φ r) i = e i

end ApproxSeq

end SennottDP.ContinuousTime
