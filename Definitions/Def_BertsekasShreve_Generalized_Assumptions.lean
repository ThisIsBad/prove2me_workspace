import Mathlib
import Definitions.Def_BertsekasShreve_Generalized_Model

namespace BertsekasShreve.Generalized

open Filter Topology

namespace Model

variable {S C : Type*} (P : Model S C)

/-- Condition A.1 (p. 93): for each `x ∈ S` and `u ∈ U(x)` there is a `μ ∈ M̃` with `μ(x) = u`. -/
def A1 : Prop := ∀ x, ∀ u ∈ P.U x, ∃ μ ∈ P.Mtil, μ x = u

/-- Condition A.2 (p. 93): for all `J ∈ F*` and `r ∈ R`, `T(J) ∈ F*` and `J + r ∈ F*`. -/
def A2 : Prop := ∀ J ∈ P.Fstar, P.T J ∈ P.Fstar ∧ ∀ r : ℝ, addConst J r ∈ P.Fstar

/-- Condition A.3 (p. 93): for all `J ∈ F̃`, `μ ∈ M̃` and `r ∈ R`, `T_μ(J) ∈ F̃` and `J + r ∈ F̃`. -/
def A3 : Prop :=
  ∀ J ∈ P.Ftil, (∀ μ ∈ P.Mtil, P.Tmu μ J ∈ P.Ftil) ∧ ∀ r : ℝ, addConst J r ∈ P.Ftil

/-- Condition A.4 (p. 93): for each `J ∈ F*` and `ε > 0` there is a `μ_ε ∈ M̃` such that for all
`x ∈ S`, `T_{μ_ε}(J)(x) ≤ T(J)(x) + ε` if `T(J)(x) > −∞` and `T_{μ_ε}(J)(x) ≤ −1/ε` if
`T(J)(x) = −∞`. -/
def A4 : Prop :=
  ∀ J ∈ P.Fstar, ∀ ε : ℝ, 0 < ε → ∃ μ ∈ P.Mtil, ∀ x,
    (⊥ < P.T J x → P.Tmu μ J x ≤ P.T J x + (ε : EReal)) ∧
    (P.T J x = ⊥ → P.Tmu μ J x ≤ ((-1 / ε : ℝ) : EReal))

/-- Condition A.5 (p. 93): the pointwise limit (in `[−∞, ∞]`) of every pointwise convergent
sequence in `F̃` lies in `F̃`; if moreover the sequence lies in `F*`, the limit lies in `F*`. -/
def A5 : Prop :=
  ∀ (Js : ℕ → S → EReal) (J : S → EReal), (∀ k, Js k ∈ P.Ftil) →
    (∀ x, Tendsto (fun k => Js k x) atTop (𝓝 (J x))) →
    J ∈ P.Ftil ∧ ((∀ k, Js k ∈ P.Fstar) → J ∈ P.Fstar)

/-- Assumption F̃.2 (p. 94) = Assumption F.2 (p. 40) with `F` replaced by `F̃`: there is a scalar
`α ∈ (0, ∞)` such that for all `r ∈ (0, ∞)` and `J ∈ F̃`,
`H(x, u, J) ≤ H(x, u, J + r) ≤ H(x, u, J) + α r` for all `x ∈ S`, `u ∈ U(x)`. -/
def Ftilde2 : Prop :=
  ∃ α : ℝ, 0 < α ∧ ∀ r : ℝ, 0 < r → ∀ J ∈ P.Ftil, ∀ x, ∀ u ∈ P.U x,
    P.H x u J ≤ P.H x u (addConst J r) ∧
    P.H x u (addConst J r) ≤ P.H x u J + ((α * r : ℝ) : EReal)

/-- Assumption F̃.3 (p. 95) = Assumption F.3 (p. 40) with `J ∈ F*`, `{J_n} ⊂ F̃`, `{μ_n} ⊂ M̃`.
The book's index `n = 1, 2, …` is Lean's `k = n − 1 = 0, 1, …`: `Js k = J_{k+1}`,
`ε k = ε_{k+1}`, `μs k = μ_{k+1}`.

There is a scalar `β ∈ (0, ∞)` such that if `J ∈ F*`, `{J_n} ⊂ F̃` and real `{ε_n}` satisfy
`Σ ε_n < ∞`, `ε_n > 0`; `J = lim J_n` (pointwise), `J ≤ J_n`;
`J_n(x) ≤ J(x) + ε_n` (`n ≥ 1`, `J(x) > −∞`), `J_n(x) ≤ J_{n−1}(x) + ε_n` (`n ≥ 2`, `J(x) = −∞`);
`H(x, u, J_1) < ∞` for all `x ∈ S`, `u ∈ U(x)`; then there is `{μ_n} ⊂ M̃` with
`lim T_{μ_n}(J_n) = T(J)`, `T_{μ_n}(J_n)(x) ≤ T(J)(x) + β ε_n` (`n ≥ 1`, `T(J)(x) > −∞`) and
`T_{μ_n}(J_n)(x) ≤ T_{μ_{n−1}}(J_{n−1})(x) + β ε_n` (`n ≥ 2`, `T(J)(x) = −∞`). -/
def Ftilde3 : Prop :=
  ∃ β : ℝ, 0 < β ∧ ∀ J ∈ P.Fstar, ∀ (Js : ℕ → S → EReal) (ε : ℕ → ℝ),
    (∀ k, Js k ∈ P.Ftil) →
    Summable ε → (∀ k, 0 < ε k) →
    (∀ x, Tendsto (fun k => Js k x) atTop (𝓝 (J x))) →
    (∀ k, J ≤ Js k) →
    (∀ k x, ⊥ < J x → Js k x ≤ J x + (ε k : EReal)) →
    (∀ k x, J x = ⊥ → Js (k + 1) x ≤ Js k x + (ε (k + 1) : EReal)) →
    (∀ x, ∀ u ∈ P.U x, P.H x u (Js 0) < ⊤) →
    ∃ μs : ℕ → S → C, (∀ k, μs k ∈ P.Mtil) ∧
      (∀ x, Tendsto (fun k => P.Tmu (μs k) (Js k) x) atTop (𝓝 (P.T J x))) ∧
      (∀ k x, ⊥ < P.T J x → P.Tmu (μs k) (Js k) x ≤ P.T J x + ((β * ε k : ℝ) : EReal)) ∧
      (∀ k x, P.T J x = ⊥ →
        P.Tmu (μs (k + 1)) (Js (k + 1)) x ≤
          P.Tmu (μs k) (Js k) x + ((β * ε (k + 1) : ℝ) : EReal))

/-- The Exact Selection Assumption (p. 95): for every `J ∈ F*`, if the infimum in
`T(J)(x) = inf_{u ∈ U(x)} H(x, u, J)` is attained for every `x ∈ S`, then there is a `μ* ∈ M̃`
with `T_{μ*}(J) = T(J)`. -/
def ExactSelection : Prop :=
  ∀ J ∈ P.Fstar, (∀ x, ∃ u ∈ P.U x, P.H x u J = P.T J x) →
    ∃ μ ∈ P.Mtil, P.Tmu μ J = P.T J

/-- Assumption C̃ (p. 96), with the closed set `B̄` and the scalars `m`, `ρ`, `α` it introduces
made explicit parameters. Membership in `B̄ ∩ F*` and `B̄ ∩ F̃` is `MemBbarInter`.

* `Bbar` is a closed subset of `B` (sup-norm topology of `ℓ^∞(S, ℝ)`);
* (a) `J₀ ∈ B̄ ∩ F*`;
* (b) for all `J ∈ B̄ ∩ F*`, `T(J) ∈ B̄ ∩ F*`;
* (c) for all `J ∈ B̄ ∩ F̃` and `μ ∈ M̃`, `T_μ(J) ∈ B̄ ∩ F̃`;
* for every `π ∈ Π̃` the limit `lim_{N → ∞} (T_{μ₀} ⋯ T_{μ_{N−1}})(J₀)(x)` exists and is a real
  number for each `x ∈ S`;
* `m` is a positive integer, `0 < ρ < 1`, `0 < α`;
* `‖T_μ(J) − T_μ(J')‖ ≤ α ‖J − J'‖` for all `μ ∈ M̃` and `J, J' ∈ B ∩ F̃` (not only `B̄ ∩ F̃`);
* `‖(T_{μ₀} ⋯ T_{μ_{m−1}})(J) − (T_{μ₀} ⋯ T_{μ_{m−1}})(J')‖ ≤ ρ ‖J − J'‖` for all
  `μ₀, …, μ_{m−1} ∈ M̃` and `J, J' ∈ B̄ ∩ F̃`; the tuple is the first `m` entries of a `π ∈ Π̃`. -/
structure AssumptionCtilde (Bbar : Set (BertsekasShreve.Contraction.BFun S)) (m : ℕ) (ρ α : ℝ) : Prop where
  isClosed : IsClosed Bbar
  J0_mem : MemBbarInter Bbar P.Fstar P.J0
  T_mem : ∀ J, MemBbarInter Bbar P.Fstar J → MemBbarInter Bbar P.Fstar (P.T J)
  Tmu_mem : ∀ μ ∈ P.Mtil, ∀ J, MemBbarInter Bbar P.Ftil J → MemBbarInter Bbar P.Ftil (P.Tmu μ J)
  limit_real : ∀ (π : P.Policy) (x : S), ∃ r : ℝ,
    Tendsto (fun N => P.comp π N P.J0 x) atTop (𝓝 (r : EReal))
  m_pos : 0 < m
  ρ_pos : 0 < ρ
  ρ_lt_one : ρ < 1
  α_pos : 0 < α
  lipschitz : ∀ μ ∈ P.Mtil, ∀ J J' : BertsekasShreve.Contraction.BFun S, BertsekasShreve.Contraction.toF J ∈ P.Ftil → BertsekasShreve.Contraction.toF J' ∈ P.Ftil →
    BertsekasShreve.Contraction.SupDistLe (P.Tmu μ (BertsekasShreve.Contraction.toF J)) (P.Tmu μ (BertsekasShreve.Contraction.toF J')) (α * ‖J - J'‖)
  contraction : ∀ (π : P.Policy), ∀ J ∈ Bbar, ∀ J' ∈ Bbar, BertsekasShreve.Contraction.toF J ∈ P.Ftil → BertsekasShreve.Contraction.toF J' ∈ P.Ftil →
    BertsekasShreve.Contraction.SupDistLe (P.comp π m (BertsekasShreve.Contraction.toF J)) (P.comp π m (BertsekasShreve.Contraction.toF J')) (ρ * ‖J - J'‖)

end Model

end BertsekasShreve.Generalized
