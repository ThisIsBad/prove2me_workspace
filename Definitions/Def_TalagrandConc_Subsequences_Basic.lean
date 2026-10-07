import Mathlib
import Definitions.Def_TalagrandConc_BinPacking_Basic

namespace TalagrandConc.Subsequences

open MeasureTheory
open scoped ENNReal

/-- Talagrand (1995), p. 153, §7.1: the length `L_N(x_1, …, x_N)` of the longest increasing
subsequence of `x`, i.e. the largest integer `p` such that there are indices
`i_1 < ⋯ < i_p` with `x_{i_1} ≤ ⋯ ≤ x_{i_p}` (weak inequalities, as printed). The indices are a
strictly increasing map `i : Fin p → Fin N` and the condition is that `x ∘ i` is monotone. The
set of admissible `p` contains `0` and is bounded by `N`, so `sSup` is its maximum. -/
noncomputable def lis {α : Type*} [LinearOrder α] {N : ℕ} (x : Fin N → α) : ℕ :=
  sSup {p : ℕ | ∃ i : Fin p → Fin N, StrictMono i ∧ Monotone (x ∘ i)}

/-- Talagrand (1995), p. 154, §7.2: the length `L_{N,N'}(x; y)` of the longest common
subsequence of `x = (x_1, …, x_N)` and `y = (y_1, …, y_{N'})`: the largest integer `p` for which
there are `1 ≤ i_1 < ⋯ < i_p ≤ N` and `1 ≤ j_1 < ⋯ < j_p ≤ N'` with `x_{i_ℓ} = y_{j_ℓ}` for each
`ℓ ≤ p`. The set of admissible `p` contains `0` and is bounded by `N`, so `sSup` is its
maximum. -/
noncomputable def lcs {α : Type*} {N N' : ℕ} (x : Fin N → α) (y : Fin N' → α) : ℕ :=
  sSup {p : ℕ | ∃ i : Fin p → Fin N, ∃ j : Fin p → Fin N',
    StrictMono i ∧ StrictMono j ∧ ∀ l, x (i l) = y (j l)}

/-- Talagrand (1995), p. 155, proof of Theorem 7.2.1: for `x ∈ Ω^{N+N'}`,
`L(x) = L_{N,N'}(x_1, …, x_N; x_{N+1}, …, x_{N+N'})`: the first `N` coordinates form the first
sequence and the last `N'` coordinates the second. -/
noncomputable def lcsJoint {α : Type*} {N N' : ℕ} (x : Fin (N + N') → α) : ℕ :=
  lcs (fun i : Fin N => x (Fin.castAdd N' i)) (fun j : Fin N' => x (Fin.natAdd N j))

/-- Talagrand (1995), p. 153 (and p. 155): the level set `A(a) = { x ; L(x) ≤ a }` of an
integer-valued function `L`. The paper introduces it for `a > 0`; that restriction is carried
by the statements that use it. -/
def levelSet {β : Type*} (L : β → ℕ) (a : ℝ) : Set β :=
  {x | (L x : ℝ) ≤ a}

open Classical in
/-- Talagrand (1995), Eq. (7.1.7), p. 154: `L_N : Ω^N → ℕ` is a *configuration function* if,
given any `x ∈ Ω^N`, there is a subset `J` of the coordinates with `card J = L_N(x)` such that
for each `y ∈ Ω^N`, `L_N(y) ≥ card { i ∈ J ; y_i = x_i }`. -/
def IsConfigurationFunction {Ω : Type*} {N : ℕ} (L : (Fin N → Ω) → ℕ) : Prop :=
  ∀ x : Fin N → Ω, ∃ J : Finset (Fin N), J.card = L x ∧
    ∀ y : Fin N → Ω, (J.filter (fun i => y i = x i)).card ≤ L y

end TalagrandConc.Subsequences
