import Mathlib

namespace AppliedComb.Polya

open MvPolynomial

/-- Keller–Trotter, Section 15.4.1 (p. 299). For a permutation `σ` of a finite set `S` and
`k ≥ 1`, `cycleCount σ k` is `j_k`, the number of cycles of length `k` in the cycle notation of
`σ` (Section 15.2.1). Fixed points are cycles of length `1` (the book writes `π = (1245)(3)`),
so `j_1` is the number of fixed points; Mathlib's `Equiv.Perm.cycleType` omits them and lists
only the cycles of length `≥ 2`. -/
def cycleCount {S : Type*} [Fintype S] [DecidableEq S] (σ : Equiv.Perm S) (k : ℕ) : ℕ :=
  if k = 1 then Fintype.card {x : S // σ x = x} else σ.cycleType.count k

/-- Keller–Trotter, Section 15.4.1 (p. 299). The monomial associated with a permutation `σ` of
an `r`-element set `S` (`r = |S|`) with `j_k` cycles of length `k` for `1 ≤ k ≤ r`:
`x_1^{j_1} x_2^{j_2} ⋯ x_r^{j_r}`. The variable `X i` with index `i : Fin r` stands for
`x_{i+1}`. -/
noncomputable def cycleMonomial {S : Type*} [Fintype S] [DecidableEq S] (σ : Equiv.Perm S) :
    MvPolynomial (Fin (Fintype.card S)) ℚ :=
  ∏ i : Fin (Fintype.card S), X i ^ cycleCount σ (i.val + 1)

open Classical in
/-- Keller–Trotter, Section 15.4.1 (pp. 300–301). The cycle index `P_G(x_1, …, x_r)` of a
permutation group `G` of a finite set `S` with `|S| = r` (Section 15.2: a set of permutations of
`S` containing the identity and closed under composition and inverses, i.e. a subgroup of
`Equiv.Perm S`): the average, over the permutations `σ ∈ G`, of the monomials
`x_1^{j_1(σ)} ⋯ x_r^{j_r(σ)}` associated with them,
`P_G = (1/|G|) ∑_{σ ∈ G} x_1^{j_1(σ)} ⋯ x_r^{j_r(σ)}`, a polynomial with rational coefficients
in the `r` variables `x_1, …, x_r`. -/
noncomputable def cycleIndex {S : Type*} [Fintype S] [DecidableEq S]
    (G : Subgroup (Equiv.Perm S)) : MvPolynomial (Fin (Fintype.card S)) ℚ :=
  (Nat.card G : ℚ)⁻¹ • ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm S => σ ∈ G), cycleMonomial σ

end AppliedComb.Polya
