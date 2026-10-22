import Mathlib
import Definitions.Def_KumarSeidman_CAF_Trajectory

namespace KumarSeidman.CAF

variable {P M : ℕ} {S : System P M}

namespace Trajectory

/-- Buffer `b` is **demanding** at time `t`: it is nonempty, or its inflow starts at `t`
(`u_b(t) < u_b(σ)` for every `σ > t`). This is the reading of "nonempty" in Definition 1
(p. 290) under which the paper's own example trajectories are clearing trajectories. -/
def Demanding (T : Trajectory S) (b : Buffer S) (t : ℝ) : Prop :=
  0 < T.x b t ∨ ∀ σ : ℝ, t < σ → inflow S T.y b t < inflow S T.y b σ

/-- **Clearing policy** (Definition 1, p. 290). For every machine `m` and every run `k` of
`m`, on buffer `b = β m k`, with processing phase starting at `a_k = s_k + δ_{β_{k-1},β_k}`:
1. (no early exit) at no time `t` with `a_k < t < s_{k+1}` (or `a_k < t` if run `k` is the
   last) is `b` empty while some other buffer `b' ∈ B_m` is demanding;
2. (exit) if run `k + 1` exists, then at its start `s_{k+1}` the buffer `b` is empty, and
   the newly selected buffer `β m (k+1) ≠ b` is demanding.
Together these force the switch at the first time after `a_k` at which `b` is empty and some
other buffer of `B_m` is demanding. -/
def IsClearing (T : Trajectory S) : Prop :=
  ∀ (m : Fin M) (k : ℕ), (k : ℕ∞) < T.N m →
    (∀ t : ℝ, T.procStart m k < t → (T.HasNext m k → t < T.s m (k + 1)) →
      ¬ (T.x (T.β m k) t = 0 ∧ ∃ b' ∈ S.B m, b' ≠ T.β m k ∧ T.Demanding b' t)) ∧
    (T.HasNext m k →
      T.x (T.β m k) (T.s m (k + 1)) = 0 ∧ T.β m (k + 1) ≠ T.β m k ∧
        T.Demanding (T.β m (k + 1)) (T.s m (k + 1)))

/-- **Clear-a-fraction (CAF) policy** (Definition 2, p. 290) with constants `ε_m > 0` and
`K_m ∈ ℝ`: a clearing trajectory such that whenever machine `m` commences a set-up to buffer
`b_{p,i}` (the start `s_k` of a run `k ≥ 1`), (2) holds:
`x_{p,i}(s_k) ≥ ε_m Σ_{(q,j): μ_{q,j} = m} x_{q,j}(s_k) − K_m`. -/
def IsCAF (T : Trajectory S) (ε K : Fin M → ℝ) : Prop :=
  T.IsClearing ∧ (∀ m, 0 < ε m) ∧
    ∀ (m : Fin M) (k : ℕ), 1 ≤ k → (k : ℕ∞) < T.N m →
      ε m * ∑ b ∈ S.B m, T.x b (T.s m k) - K m ≤ T.x (T.β m k) (T.s m k)

end Trajectory

end KumarSeidman.CAF
