import Definitions.Def_matrix_completion_bernoulli
open MatrixCompletion

namespace CandesTao.LowerBound

theorem all_rows_sampled_prob (n ℓ : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (S : Fin n → Finset (Fin n × Fin n))
    (hdisj : Pairwise (fun a b => Disjoint (S a) (S b)))
    (hcard : ∀ a, (S a).card = ℓ) :
    bernoulliEventProb p (fun Ω : Finset (Fin n × Fin n) => ∀ a, ∃ e ∈ S a, e ∈ Ω) =
      (1 - (1 - p) ^ ℓ) ^ n := by sorry

end CandesTao.LowerBound
