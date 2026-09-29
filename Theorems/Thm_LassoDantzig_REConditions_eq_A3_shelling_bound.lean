import Mathlib
import Definitions.Def_LassoDantzig_REConditions_RE
import Definitions.Def_LassoDantzig_REConditions_RestrictedEigenvalues

namespace LassoDantzig.REConditions

/-- **(A.3)**, Bickel–Ritov–Tsybakov, arXiv:0801.1095v3, Appendix A, pp. 19–20. Let
`J0ᶜ = J 1 ∪ ⋯ ∪ J K` be the partition into consecutive blocks of `m` largest `|δ_j|`
(`IsShelling`). Then `|δ_{J(k+1)}|₂ ≤ |δ_{Jk}|₁/√m` for `k = 1, …, K−1`, hence
`∑_{k=2}^K |δ_{Jk}|₂ ≤ |δ_{J0ᶜ}|₁/√m`; and if moreover `|J0| ≤ s` and the cone condition (4.1)
holds, `|δ_{J0ᶜ}|₁/√m ≤ c₀|δ_{J0}|₁/√m ≤ c₀√(s/m)|δ_{J0}|₂ ≤ c₀√(s/m)|δ_{J01}|₂`, `J01 = J0 ∪ J 1`. -/
theorem eq_A3_shelling_bound {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M)
    (s m : ℕ) (hm : 1 ≤ m) (c0 : ℝ) (hc0 : 0 < c0)
    (δ : Fin M → ℝ) (J0 : Finset (Fin M)) (J : ℕ → Finset (Fin M)) (K : ℕ)
    (hsh : IsShelling δ J0 m J K) :
    (∀ k ∈ Finset.Ico 1 K, l2On δ (J (k + 1)) ≤ l1On δ (J k) / Real.sqrt m) ∧
    ∑ k ∈ Finset.Icc 2 K, l2On δ (J k) ≤ l1On δ J0ᶜ / Real.sqrt m ∧
    (J0.card ≤ s → ConeCond c0 J0 δ →
      l1On δ J0ᶜ / Real.sqrt m ≤ c0 * l1On δ J0 / Real.sqrt m ∧
      c0 * l1On δ J0 / Real.sqrt m ≤ c0 * Real.sqrt ((s : ℝ) / m) * l2On δ J0 ∧
      c0 * Real.sqrt ((s : ℝ) / m) * l2On δ J0 ≤
        c0 * Real.sqrt ((s : ℝ) / m) * l2On δ (J0 ∪ J 1)) := by sorry

end LassoDantzig.REConditions
