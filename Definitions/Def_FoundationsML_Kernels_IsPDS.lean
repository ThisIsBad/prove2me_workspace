import Mathlib

namespace FoundationsML.Kernels

/-- A kernel `K : X × X → ℝ` is positive definite symmetric (PDS) (Mohri, Rostamizadeh &
Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, Definition 6.3, p. 108,
PDF p. 125): `K` is symmetric, and for any finite set of points `{x_1,…,x_m} ⊆ X` and any
`c_1,…,c_m ∈ ℝ`, `∑_{i,j} c_i c_j K(x_i,x_j) ≥ 0` — i.e. the kernel matrix `[K(x_i,x_j)]` is
symmetric positive semidefinite (SPSD) for every finite sample.

**Formalization Note.** Uses the book's own second SPSD characterization
(`c^T K c ≥ 0` for every `c`, Definition 6.3's displayed condition (6.2)) rather than the
non-negative-eigenvalues characterization, since it avoids spectral theory for a `Prop`-valued
definition; the book states the two are equivalent. -/
def IsPDS {X : Type*} (K : X → X → ℝ) : Prop :=
  (∀ x y : X, K x y = K y x) ∧
  ∀ (S : Finset X) (c : X → ℝ), 0 ≤ ∑ i ∈ S, ∑ j ∈ S, c i * c j * K i j

end FoundationsML.Kernels
