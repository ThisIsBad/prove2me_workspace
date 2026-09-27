import Mathlib

namespace HighDimStat.SparseLinear

/-- The pairwise incoherence parameter `δ_PW(X) := max_{j,k} |⟨Xⱼ,Xₖ⟩/n − 𝟙[j=k]|` of
Wainwright, *High-Dimensional Statistics* (2019), Eq. (7.12), p. 203, where `Xⱼ` denotes the
`j`-th column of `X`. Realized as `⨆` over the finite index type `Fin d × Fin d`; at `d = 0`
this is Mathlib's junk value `0`. -/
noncomputable def pairwiseIncoherence {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) : ℝ :=
  ⨆ jk : Fin d × Fin d,
    |(∑ i, X i jk.1 * X i jk.2) / (n : ℝ) - (if jk.1 = jk.2 then (1 : ℝ) else 0)|

end HighDimStat.SparseLinear
