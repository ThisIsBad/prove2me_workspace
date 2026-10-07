import Mathlib

namespace LawlerMoore.PrecDeadline

/-- The modified deadline of Lawler and Moore (1969, §2, p. 78):
`d̄_j = min {d_k | j ρ k} + j ε`.

Jobs are `Fin n`, 0-based: the Lean job `j` is the paper's job `j + 1`, so the tie-breaking term
`j ε` of the paper is `((j : ℕ) + 1) * ε` here. `ρ j k` means that job `j` must precede job `k`.
The minimum runs over the successors of `j` *including `j` itself* ("considering a job to be one
of its own successors", p. 78); for the reflexive relation of the paper the set
`insert j {k | ρ j k}` is exactly `{k | ρ j k}`, and inserting `j` makes the minimum range over a
nonempty set for every relation. -/
def modifiedDeadline {n : ℕ} (ρ : Fin n → Fin n → Prop) [DecidableRel ρ] (d : Fin n → ℝ)
    (ε : ℝ) (j : Fin n) : ℝ :=
  (insert j (Finset.univ.filter (ρ j))).inf' (Finset.insert_nonempty _ _) d
    + ((j : ℕ) + 1 : ℝ) * ε

end LawlerMoore.PrecDeadline
