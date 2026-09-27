import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core

/-!
Bellman rank (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive
Decision Making*, arXiv:2312.16730v1, §7.3, Definition 8, p. 138): the Bellman residual of a
state-action value function `Q` (a family of layer functions `Q h : S → A → ℝ`, with the
book's terminal convention `Q_{H+1} ≡ 0` imposed explicitly rather than read off `Q H`) under
a policy `π`, and the Bellman rank of an MDP `M` relative to a value-function class `𝒬` as the
*least* dimension `d` admitting the book's bilinear factorization (7.24) at every layer — an
actual rank, per the book's own "Equivalently, Bellman rank is the smallest dimension `d`
such that …", not an unconstrained parameter. Reuses `EpisodicMDP`, `Policy`, `IsPolicy`,
`stateDist` from the published `RLBasics.Core`.
-/

namespace FoundationsRL.FuncApprox

open FoundationsRL.RLBasics

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] {H : ℕ}

/-- Expectation of a state-action function `f` under the layer-`h` state-action marginal
induced by `M`, `π`, starting from `M.d1` (Foster–Rakhlin write `E^{M,π}[f(s_h,a_h)]`). -/
noncomputable def layerStateActionExp (M : EpisodicMDP S A H) (π : Policy S A H) (h : ℕ)
    (f : S → A → ℝ) : ℝ :=
  ∑ s0 : S, M.d1 s0 * ∑ s : S, stateDist M π s0 h s * ∑ a : A, π h s a * f s a

/-- The Bellman residual `E_h(π, Q) = E^{M,π}[Q_h(s_h,a_h) - r_h - max_a Q_{h+1}(s_{h+1},a)]`
(Foster–Rakhlin, p. 138, Eq. (7.22)), for a family `Q : ℕ → S → A → ℝ` of layer value
functions, with `Q_{H+1} ≡ 0` imposed at the horizon. The realized reward `r_h` is replaced by
its conditional mean `M.R h s a`: exact, not approximate, by the tower property
`E[r_h ∣ s_h,a_h] = M.R h s_h a_h`, regardless of whether the reward itself is random. -/
noncomputable def bellmanResidual (M : EpisodicMDP S A H) (π : Policy S A H) (h : ℕ)
    (Q : ℕ → S → A → ℝ) : ℝ :=
  layerStateActionExp M π h
    (fun s a => Q h s a -
      (M.R h s a + ∑ s' : S, M.P h s a s' * (if h + 1 < H then ⨆ a' : A, Q (h + 1) s' a' else 0)))

/-- `M` admits a Bellman-rank-`≤ d` bilinear factorization for the value-function class `𝒬`
(Foster–Rakhlin, p. 138: "Equivalently, Bellman rank is the smallest dimension `d` such that
for all `h`, there exist embeddings `X^M_h(π), W^M_h(Q) ∈ ℝ^d` such that …"): at every layer
`h < H`, the residual `E_h(π, Q)` factors as `⟨X_h(π), W_h(Q)⟩` for embeddings into `ℝ^d`. -/
def HasBellmanRankLE (M : EpisodicMDP S A H) (𝒬 : Set (ℕ → S → A → ℝ)) (d : ℕ) : Prop :=
  ∃ (X : Policy S A H → ℕ → Fin d → ℝ) (W : (ℕ → S → A → ℝ) → ℕ → Fin d → ℝ),
    ∀ π : Policy S A H, IsPolicy H π → ∀ Q ∈ 𝒬, ∀ h : ℕ, h < H →
      bellmanResidual M π h Q = ∑ j : Fin d, X π h j * W Q h j

/-- `M` has Bellman rank exactly `d` relative to `𝒬` (Definition 8, p. 138): `d` is the
*least* natural number admitting a `HasBellmanRankLE` factorization. -/
def IsBellmanRank (M : EpisodicMDP S A H) (𝒬 : Set (ℕ → S → A → ℝ)) (d : ℕ) : Prop :=
  IsLeast {d' : ℕ | HasBellmanRankLE M 𝒬 d'} d

/-- The squared elliptic norm `‖v‖²_Σ` of `v ∈ ℝ^d` with respect to the Gram matrix
`Σ = ∑_{x ∈ xs} x xᵀ` built from a list of vectors `xs`, expressed via the standard identity
`‖v‖²_Σ = ∑_{x ∈ xs} ⟨x, v⟩²` — this is the quantity `Σ^k_h` is built from throughout §7.3.2
(Lemma 30, Lemma 31), without introducing `Matrix`/matrix-inverse machinery. -/
def elliptNormSq {d : ℕ} (xs : List (Fin d → ℝ)) (v : Fin d → ℝ) : ℝ :=
  (xs.map (fun x => (∑ j : Fin d, x j * v j) ^ 2)).sum

end FoundationsRL.FuncApprox
