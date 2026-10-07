import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_KallenbergLP_Constrained_Frequencies

namespace KallenbergLP.Constrained

open MarkovDecisionProcesses Filter Topology

/-- Kallenberg (1983), Lemma 4.7.1, pp. 153–154: for `R ∈ C_1` with unique limit point `x(R)` and
every pair `(j, a)`,
`x_{ja}(R) = lim_{α↑1} (1−α) ∑_{t=1}^∞ α^{t−1} ∑_i β_i ℙ_R(X_t = j, Y_t = a | X_1 = i)`. -/
theorem freq_eq_abel_limit {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]
    [DecidableEq A] (M : StationaryMDP S A) (β : S → ℝ) (hβ0 : ∀ j, 0 ≤ β j)
    (hβ1 : ∑ j, β j = 1) (R : AvgHRPolicy M) (hR : IsC1 β R)
    (x : KallenbergLP.AverageLP.Pair M → ℝ) (hx : x ∈ limitPoints β R) (p : KallenbergLP.AverageLP.Pair M) :
    Tendsto (fun α : ℝ => (1 - α) * ∑' k : ℕ, α ^ k * ∑ i, β i * prob R k i p)
      (𝓝[<] 1) (𝓝 (x p)) := by sorry

end KallenbergLP.Constrained

