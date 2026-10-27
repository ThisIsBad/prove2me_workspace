import Mathlib

namespace CrossSell.Pricing
open Finset

variable {ι κ : Type*}

/-- Stage-1 denominator `1 + Σ_{j∈S} exp(u_j − p_j)` of eq. (1). -/
noncomputable def mainDenom (S : Finset ι) (u p : ι → ℝ) : ℝ :=
  1 + ∑ j ∈ S, Real.exp (u j - p j)

/-- `d_i(S, p)` of eq. (1) on `S+ = S ∪ {0}`, encoded in `Option ι`: `none` is the no-purchase
option `0`, with `d_0 = 1 − Σ_{i∈S} d_i = 1 / (1 + Σ_{j∈S} exp(u_j − p_j))`. -/
noncomputable def mainProb (S : Finset ι) (u p : ι → ℝ) : Option ι → ℝ
  | none => 1 / mainDenom S u p
  | some i => Real.exp (u i - p i) / mainDenom S u p

/-- The stage-1 margin `p_i − c_i` on `S+`, with `p_0 − c_0 = 0` (eq. (6)). -/
def mainMargin (c p : ι → ℝ) : Option ι → ℝ
  | none => 0
  | some i => p i - c i

/-- `q_{l|i}(T_i, r)` of eq. (3). -/
noncomputable def secProb (T : Option ι → Finset κ) (v : Option ι → κ → ℝ) (r : κ → ℝ)
    (i : Option ι) (l : κ) : ℝ :=
  Real.exp (v i l - r l) / (1 + ∑ k ∈ T i, Real.exp (v i k - r k))

/-- `t_i` of Definition 1: the profit collected from the secondary set `T_i`, for `i ∈ S+`. -/
noncomputable def secProfit (T : Option ι → Finset κ) (s : κ → ℝ) (v : Option ι → κ → ℝ)
    (r : κ → ℝ) (i : Option ι) : ℝ :=
  ∑ l ∈ T i, (r l - s l) * secProb T v r i l

/-- The total expected profit `Π(S, T, p, r)` of eq. (5). -/
noncomputable def profit (S : Finset ι) (T : Option ι → Finset κ) (u c : ι → ℝ) (s : κ → ℝ)
    (v : Option ι → κ → ℝ) (p : ι → ℝ) (r : κ → ℝ) : ℝ :=
  (∑ i ∈ S, (p i - c i) * mainProb S u p (some i)) +
    ∑ i ∈ S.insertNone, ∑ l ∈ T i, (r l - s l) * mainProb S u p i * secProb T v r i l

/-- The aggregate markup `p_i − c_i + t_i` of Definition 1. -/
noncomputable def aggMarkup (T : Option ι → Finset κ) (c : ι → ℝ) (s : κ → ℝ)
    (v : Option ι → κ → ℝ) (p : ι → ℝ) (r : κ → ℝ) (i : ι) : ℝ :=
  p i - c i + secProfit T s v r (some i)

/-- `H(r; z)` of Theorem 1. -/
noncomputable def Hr (S : Finset ι) (T : Option ι → Finset κ) (u c : ι → ℝ) (s : κ → ℝ)
    (v : Option ι → κ → ℝ) (r : κ → ℝ) (z : ℝ) : ℝ :=
  (∑ i ∈ S, Real.exp ((u i - c i - 1 - z) + secProfit T s v r (some i))) +
    secProfit T s v r none

/-- `H(z) := max_r H(r; z)` of Theorem 1, as a real supremum over all secondary price vectors.
Every statement that uses it also asserts that the range is bounded above. -/
noncomputable def Hmax (S : Finset ι) (T : Option ι → Finset κ) (u c : ι → ℝ) (s : κ → ℝ)
    (v : Option ι → κ → ℝ) (z : ℝ) : ℝ :=
  ⨆ r : κ → ℝ, Hr S T u c s v r z

end CrossSell.Pricing
