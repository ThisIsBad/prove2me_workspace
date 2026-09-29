import Mathlib

/-!
# Subpermutation density and convergent permutation sequences

C. Hoppen, Y. Kohayakawa, C. G. Moreira, B. Ráth, R. M. Sampaio, *Limits of permutation
sequences*, arXiv:1103.5844v2, p. 3, Definitions 1.1 and 1.2, Eq. (3).

A definition bundle: the number of occurrences `Λ(τ, π)`, the density `t(τ, π)`, and the notion of
a convergent permutation sequence.

**Formalization Note.** The paper's `S_n` (permutations of `[n] = {1, …, n}`) is
`Equiv.Perm (Fin n)`, i.e. permutations of `{0, …, n-1}`; the shift by one changes no relative
order, so `Λ` and `t` are unchanged. A permutation of arbitrary length (an element of the paper's
`𝒮 = ⋃ₙ Sₙ`) is a dependent pair `⟨n, π⟩ : Σ n : ℕ, Equiv.Perm (Fin n)`, and a permutation
sequence is a map `ℕ → Σ n : ℕ, Equiv.Perm (Fin n)`; `|σ_m|` is `(σ m).1`. Length `0` is allowed
by the type. A length-`0` pattern `τ` has `t(τ, π) = 1` for every `π` (and `t(τ, Z) = 1` for every
limit permutation), so quantifying over all `k`, including `k = 0`, adds only a trivially
satisfied clause.
-/

namespace PermLimits.Shared

open Filter Topology

/-- **Occurrences** `Λ(τ, π)` (Hoppen et al., arXiv:1103.5844v2, Definition 1.1, p. 3).
For `τ ∈ S_k` and `π ∈ S_n`, the number of strictly increasing `k`-tuples
`x₁ < x₂ < … < x_k` in `[n]` such that `π(x_i) < π(x_j)` if and only if `τ(i) < τ(j)`.

**Formalization Note.** A strictly increasing `k`-tuple in `[n]` is a map `x : Fin k → Fin n`
with `i < j → x i < x j`; indices are 0-based (see the module note). -/
noncomputable def occurrences {k n : ℕ} (τ : Equiv.Perm (Fin k)) (π : Equiv.Perm (Fin n)) : ℕ :=
  open Classical in
  (Finset.univ.filter (fun x : Fin k → Fin n =>
    (∀ i j, i < j → x i < x j) ∧ ∀ i j, (π (x i) < π (x j) ↔ τ i < τ j))).card

/-- **Subpermutation density** `t(τ, π)` (Hoppen et al., arXiv:1103.5844v2, Definition 1.1,
Eq. (3), p. 3): `t(τ, π) = Λ(τ, π) / C(n, k)` if `k ≤ n`, and `0` if `k > n`.

**Formalization Note.** Eq. (3) of the preprint misprints `Λ(τ, σ)` for `Λ(τ, π)`. The case
`k > n` is written explicitly (it does not rely on division by zero; for `k > n` also
`Λ(τ, π) = 0`). -/
noncomputable def permDensity {k n : ℕ} (τ : Equiv.Perm (Fin k)) (π : Equiv.Perm (Fin n)) : ℝ :=
  if k ≤ n then (occurrences τ π : ℝ) / (Nat.choose n k : ℝ) else 0

/-- **Convergent permutation sequence** (Hoppen et al., arXiv:1103.5844v2, Definition 1.2,
p. 3). A permutation sequence `(σ_m)` is convergent if, for every fixed permutation `τ`, the
sequence of real numbers `(t(τ, σ_m))_m` converges.

**Formalization Note.** No condition on the lengths `|σ_m|` is part of this definition (as in the
paper); `τ` ranges over permutations of every length `k` (see the module note on `k = 0`). -/
def IsConvergent (σ : ℕ → Σ n : ℕ, Equiv.Perm (Fin n)) : Prop :=
  ∀ (k : ℕ) (τ : Equiv.Perm (Fin k)), ∃ L : ℝ,
    Tendsto (fun m => permDensity τ (σ m).2) atTop (𝓝 L)

end PermLimits.Shared
