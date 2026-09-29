import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy
import Definitions.Def_ArrowDebreu_ThmI_AssumptionsItoIV
import Definitions.Def_ArrowDebreu_Shared_IsCompetitiveEquilibrium
import Definitions.Def_ArrowDebreu_Shared_AbstractEconomy
import Definitions.Def_ArrowDebreu_ThmI_economyE
open ArrowDebreu.Shared

namespace ArrowDebreu.ThmI

open AbstractEconomy

/-- **Remark (§3.3.5)**, Arrow & Debreu, Econometrica 22 (1954), p. 278 (PDF p. 15): "If
`p·ζ_i > min_{x_i ∈ X̃_i} p·x_i`, then `Ã_i(x̄_i)` is continuous at the point
`x̄_i = (x_1, ⋯, x_{i−1}, x_{i+1}, ⋯, x_m, y_1, ⋯, y_n, p)`."

Here `Ẽ = economyEtilde E c` is the truncated abstract economy of §3.3.4 (`X̃_i = X_i ∩ C`,
`Ỹ_j = Y_j ∩ C`, `C` the cube of half-side `c`), `Ã_i` its constraint set for consumer `i`, and
"continuous" is the sequential notion of §2.4 (`ConstrContinuousAt`), at a point `x̄_i` of
`𝔄̄_i` (others' actions in `X̃_{i'}`, `Ỹ_j`, `P`).

**Formalization Note.**
* The hypothesis `p·ζ_i > min_{X̃_i} p·x_i` is written `∃ x' ∈ X̃_i, p·x' < p·ζ_i`, which is
  equivalent whenever the minimum exists (`X̃_i` compact and nonempty) and needs no infimum.
* The paper's proof uses the convexity of `X̃_i` (from Assumption II) and, when it chooses
  `x_i^k = x_i` or `x_i(λ^k)` "for `k` sufficiently large", that `Ã_i` is non-null at every
  point of `𝔄̄_i` — established in §3.3.4 just before the Remark ("`Ã_i(x̄_i)` contains `x_i'` and
  therefore is non-null"). Both are hypotheses (`hne`). Without `hne` the statement is false:
  §2.4 asks for `a_i^k ∈ Ã_i(x̄_i^k)` for **all** `k`, which fails if some early `Ã_i(x̄_i^k)` is
  empty. `c` is an arbitrary real; no property of the §3.3.3 choice of `c` is used. -/
theorem remark_3_3_5 {l m n : ℕ} (E : Economy l m n) (hII : AssumptionII E) (c : ℝ) (i : Fin m)
    (hne : ∀ b, (economyEtilde E c).OthersIn (Sum.inl i) b →
      ((economyEtilde E c).constr (Sum.inl i) b).Nonempty)
    (a : Player m n → Fin l → ℝ) (ha : (economyEtilde E c).OthersIn (Sum.inl i) a)
    (hmin : ∃ x' ∈ E.X i ∩ cube l c, priceOf a ⬝ᵥ x' < priceOf a ⬝ᵥ E.ζ i) :
    (economyEtilde E c).ConstrContinuousAt (Sum.inl i) a := by sorry

end ArrowDebreu.ThmI
