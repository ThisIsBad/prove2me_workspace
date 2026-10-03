import Mathlib

namespace TeschlODE.HigherDim

/-- Teschl, §8.1, p. 229: the `ω₊`-limit set of a set `X ⊆ M`: the points `y ∈ M` for which
there are sequences `t_k → ∞` and `x_k ∈ X` with `Φ(t_k, x_k) → y`. Each `t_k` lies in the
existence interval `I (x_k)` of `x_k`, so `Φ(t_k, x_k)` is a value of the (local) flow. -/
def omegaPlusSet {E : Type*} [NormedAddCommGroup E] (M : Set E) (I : E → Set ℝ)
    (Φ : ℝ → E → E) (X : Set E) : Set E :=
  {y | y ∈ M ∧ ∃ (t : ℕ → ℝ) (x : ℕ → E), (∀ k, x k ∈ X ∧ t k ∈ I (x k)) ∧
    Filter.Tendsto t Filter.atTop Filter.atTop ∧
    Filter.Tendsto (fun k => Φ (t k) (x k)) Filter.atTop (nhds y)}

end TeschlODE.HigherDim
