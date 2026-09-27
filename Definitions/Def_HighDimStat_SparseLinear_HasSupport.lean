import Mathlib

namespace HighDimStat.SparseLinear

/-- `θ` is supported on `S`: every coordinate outside `S` vanishes, `θⱼ = 0` for `j ∉ S`, as in
Wainwright, *High-Dimensional Statistics* (2019), p. 200 ("the vector θ* has support S ⊂
{1,...,d}, meaning that θ*ⱼ = 0 for all j ∈ Sᶜ"). -/
def HasSupport {d : ℕ} (θ : Fin d → ℝ) (S : Finset (Fin d)) : Prop :=
  ∀ j, j ∉ S → θ j = 0

end HighDimStat.SparseLinear
