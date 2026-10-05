import Mathlib
import Definitions.Def_BertsekasShreve_FiniteHorizon_Model

namespace BertsekasShreve.FiniteHorizon

open Filter Topology

namespace Model

variable {S C : Type*} (m : Model S C)

/-- Assumption F.1 (p. 39): if `{J_k} ⊂ F` satisfies `J_{k+1} ≤ J_k` for all `k` and
`H(x, u, J₁) < ∞` for all `x ∈ S`, `u ∈ U(x)` (the first term of the sequence), then
`lim_{k→∞} H(x, u, J_k) = H(x, u, lim_{k→∞} J_k)` for all `x ∈ S`, `u ∈ U(x)`.
The sequence is indexed from `0` here, so its first term is `J 0`; `Jlim` is its pointwise
limit, which exists in `R*` because the sequence is nonincreasing. -/
def AssumptionF1 : Prop :=
  ∀ J : ℕ → S → EReal, (∀ k, J (k + 1) ≤ J k) →
    (∀ x, ∀ u ∈ m.U x, m.H x u (J 0) < ⊤) →
    ∀ Jlim : S → EReal, (∀ x, Tendsto (fun k => J k x) atTop (𝓝 (Jlim x))) →
      ∀ x, ∀ u ∈ m.U x, Tendsto (fun k => m.H x u (J k)) atTop (𝓝 (m.H x u Jlim))

/-- The inequality of Assumption F.2 for a given scalar `α`: for all scalars `r ∈ (0, ∞)` and
`J ∈ F`, `H(x, u, J) ≤ H(x, u, J + r) ≤ H(x, u, J) + α r` for all `x ∈ S`, `u ∈ U(x)`. -/
def F2With (α : ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → ∀ J : S → EReal, ∀ x, ∀ u ∈ m.U x,
    m.H x u J ≤ m.H x u (fun y => J y + (r : EReal)) ∧
      m.H x u (fun y => J y + (r : EReal)) ≤ m.H x u J + ((α * r : ℝ) : EReal)

/-- Assumption F.2 (p. 40): there exists a scalar `α ∈ (0, ∞)` for which `F2With α` holds. -/
def AssumptionF2 : Prop := ∃ α : ℝ, 0 < α ∧ m.F2With α

/-- Assumption F.3 (p. 40), with all sequences indexed by `n = 1, 2, …` (index `0` unused).
There is a scalar `β ∈ (0, ∞)` such that if `J ∈ F`, `{J_n} ⊂ F` and `{ε_n} ⊂ R` satisfy
`∑_{n=1}^∞ ε_n < ∞`, `ε_n > 0`; `J = lim J_n`, `J ≤ J_n`;
`J_n(x) ≤ J(x) + ε_n` (`n ≥ 1`, `J(x) > −∞`), `J_n(x) ≤ J_{n−1}(x) + ε_n` (`n ≥ 2`, `J(x) = −∞`);
and `H(x, u, J₁) < ∞` for all `x ∈ S`, `u ∈ U(x)`, then there is a sequence `{μ_n} ⊂ M` with
`lim T_{μ_n}(J_n) = T(J)`,
`T_{μ_n}(J_n)(x) ≤ T(J)(x) + β ε_n` (`n ≥ 1`, `T(J)(x) > −∞`), and
`T_{μ_n}(J_n)(x) ≤ T_{μ_{n−1}}(J_{n−1})(x) + β ε_n` (`n ≥ 2`, `T(J)(x) = −∞`). -/
def AssumptionF3 : Prop :=
  ∃ β : ℝ, 0 < β ∧
    ∀ (J : S → EReal) (Js : ℕ → S → EReal) (ε : ℕ → ℝ),
      Summable (fun n => ε (n + 1)) →
      (∀ n, 1 ≤ n → 0 < ε n) →
      (∀ x, Tendsto (fun n => Js n x) atTop (𝓝 (J x))) →
      (∀ n, 1 ≤ n → J ≤ Js n) →
      (∀ n, 1 ≤ n → ∀ x, J x ≠ ⊥ → Js n x ≤ J x + (ε n : EReal)) →
      (∀ n, 2 ≤ n → ∀ x, J x = ⊥ → Js n x ≤ Js (n - 1) x + (ε n : EReal)) →
      (∀ x, ∀ u ∈ m.U x, m.H x u (Js 1) < ⊤) →
      ∃ μs : ℕ → m.Selector,
        (∀ x, Tendsto (fun n => m.Tmu (μs n) (Js n) x) atTop (𝓝 (m.T J x))) ∧
        (∀ n, 1 ≤ n → ∀ x, m.T J x ≠ ⊥ →
          m.Tmu (μs n) (Js n) x ≤ m.T J x + ((β * ε n : ℝ) : EReal)) ∧
        (∀ n, 2 ≤ n → ∀ x, m.T J x = ⊥ →
          m.Tmu (μs n) (Js n) x ≤
            m.Tmu (μs (n - 1)) (Js (n - 1)) x + ((β * ε n : ℝ) : EReal))

end Model

end BertsekasShreve.FiniteHorizon
