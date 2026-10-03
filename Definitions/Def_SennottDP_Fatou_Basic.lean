import Mathlib

open Filter Topology
open scoped ENNReal

namespace SennottDP.Fatou

/-- Sennott (1999), App. A.1–A.2, pp. 270–278: the weighted sum `∑_{j ∈ S} P_j u(j)` of an
extended-real function `u` against nonnegative weights `P`, with the book's convention
`0 · ∞ = 0` (p. 270, p. 275). It is the sum of the positive parts minus the sum of the negative
parts, `∑_j P_j u(j)⁺ − ∑_j P_j u(j)⁻`, each computed in `[0, ∞]`. Whenever the negative (or the
positive) parts have a finite weighted sum this is the book's value of the series, in
`(−∞, ∞]` (resp. `[−∞, ∞)`); when both are infinite the book's sum is undefined and the value
here is `⊤ − ⊤ = ⊥` (a junk value that no statement of this mission relies on). -/
noncomputable def wsum {S : Type*} (P : S → ℝ≥0∞) (u : S → EReal) : EReal :=
  ((∑' j, P j * (u j).toENNReal : ℝ≥0∞) : EReal) - ((∑' j, P j * (-u j).toENNReal : ℝ≥0∞) : EReal)

/-- Sennott (1999), Proposition A.2.5 (i)–(iii), pp. 277–278: approximating distributions.
(i) `(P_j)_{j ∈ S}` is a probability distribution on `S`; (ii) `(S_N)` is an increasing sequence
of subsets of `S` with `⋃_N S_N = S`; (iii) for each `N`, `(P_j(N))_{j ∈ S_N}` is a probability
distribution on `S_N`, and `lim_{N → ∞} P_j(N) = P_j` for every `j ∈ S`. Here `Q N j = P_j(N)`;
its values for `j ∉ S_N` are never used (every sum is restricted to `S_N`, and a fixed `j` lies
in `S_N` for all large `N`). -/
structure ApproxDist {S : Type*} (P : S → ℝ≥0∞) (SN : ℕ → Set S) (Q : ℕ → S → ℝ≥0∞) : Prop where
  /-- (i) `∑_{j ∈ S} P_j = 1` -/
  prob : ∑' j, P j = 1
  /-- (ii) `S_N ⊆ S_{N+1}` -/
  mono : Monotone SN
  /-- (ii) `⋃_N S_N = S` -/
  iUnion_eq : ⋃ N, SN N = Set.univ
  /-- (iii) `∑_{j ∈ S_N} P_j(N) = 1` -/
  prob_N : ∀ N, ∑' j, (SN N).indicator (Q N) j = 1
  /-- (iii) `lim_{N → ∞} P_j(N) = P_j` -/
  tendsto : ∀ j, Tendsto (fun N => Q N j) atTop (𝓝 (P j))

end SennottDP.Fatou
