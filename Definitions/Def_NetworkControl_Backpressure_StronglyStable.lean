import Mathlib

namespace NetworkControl.Backpressure

/-- Definition 3.1 (p. 24), restated locally in this chunk's own sub-namespace (drafts cannot
import chunk `03-capacity-region`'s copy). A queue backlog sequence `U` (with `U t` interpreted
as `E{U(t)}`) is strongly stable if it has a bounded time-average — for a real sequence this is
equivalent to the book's `limsup < ∞` (see `03-capacity-region`'s `SELF_REVIEW.md` for the
equivalence argument), stated here in the same quantifier-light form. -/
def StronglyStable (U : ℕ → ℝ) : Prop :=
  ∃ M : ℝ, ∀ t : ℕ, (1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, U τ ≤ M

/-- Definition 3.2 (p. 24): a network of `L` queues is strongly stable if every individual queue
is. `U i` is the expected-backlog sequence of queue `i`. -/
def NetworkStronglyStable {L : ℕ} (U : Fin L → ℕ → ℝ) : Prop :=
  ∀ i : Fin L, StronglyStable (U i)

end NetworkControl.Backpressure
