import Mathlib

namespace ExplicitExpanders.Sizes

/-- The vertex count of the LPS graph `H(p, q₁ˢ q₂ᵗ)` as an explicit expression (Alon, *Explicit
expanders of every degree and size*, arXiv:2003.11673v1, §2.3, p. 6):
`Q(q₁, q₂, s, t) = q₁^{3(s−1)} q₂^{3(t−1)} · q₁(q₁−1)(q₁+1)/2 · q₂(q₂−1)(q₂+1)/2`.
It is used only for `s, t ≥ 1` (so `s - 1`, `t - 1` are the true differences) and primes `q₁, q₂`
(so `qᵢ - 1` is the true difference). Each division by `2` is exact, because `q(q−1)(q+1)` is a
product of three consecutive integers and hence even. -/
def Q (q₁ q₂ s t : ℕ) : ℕ :=
  q₁ ^ (3 * (s - 1)) * q₂ ^ (3 * (t - 1)) * (q₁ * (q₁ - 1) * (q₁ + 1) / 2) *
    (q₂ * (q₂ - 1) * (q₂ + 1) / 2)

end ExplicitExpanders.Sizes
