import Mathlib

namespace OnlineConvexOpt.FirstOrder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An online algorithm for OCO on decision set `K`: a map from a full cost-function sequence
(unknown to the algorithm in advance) to a play sequence, required to be non-anticipating
(`A f t` depends only on `f 0, ..., f (t - 1)`, matching the protocol of chapter 1/3: round `t`'s
decision is chosen after observing `f_0(x_0), ..., f_{t-1}(x_{t-1})` but before `f_t` is revealed)
and to always play inside `K`. This is the "any algorithm for online convex optimization" the
lower bound of Theorem 3.2 quantifies over. -/
def IsOnlineAlgorithm (K : Set E) (A : (ℕ → E → ℝ) → ℕ → E) : Prop :=
  (∀ f, A f 0 ∈ K) ∧ (∀ f t, A f (t + 1) ∈ K) ∧
    ∀ (f f' : ℕ → E → ℝ) (t : ℕ), (∀ s < t, f s = f' s) → A f t = A f' t

end OnlineConvexOpt.FirstOrder
