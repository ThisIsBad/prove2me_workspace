import Mathlib

namespace FoundationsML.MultiClass

/-- A positive-definite symmetric (PDS) kernel `K : X × X → ℝ` (Mohri, Rostamizadeh &
Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, referenced at p. 219,
PDF p. 236, restated locally for this chapter since drafts cannot import chunk `06-kernels`'s
own draft copy): `K` is symmetric, and for every finite set of points `x_1,…,x_n ∈ X` and
reals `c_1,…,c_n`, `∑_{i,j} c_i c_j K(x_i,x_j) ≥ 0`. -/
def IsPDS {X : Type*} (K : X → X → ℝ) : Prop :=
  (∀ x y, K x y = K y x) ∧
    ∀ (n : ℕ) (x : Fin n → X) (c : Fin n → ℝ), 0 ≤ ∑ i, ∑ j, c i * c j * K (x i) (x j)

end FoundationsML.MultiClass
