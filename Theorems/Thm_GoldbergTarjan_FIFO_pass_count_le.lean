import Mathlib
import Definitions.Def_GoldbergTarjan_FIFO_Network
import Definitions.Def_GoldbergTarjan_FIFO_PushRelabel
import Definitions.Def_GoldbergTarjan_FIFO_Algorithm
import Definitions.Def_GoldbergTarjan_FIFO_Counts

namespace GoldbergTarjan.FIFO

/-- Lemma 4.3 (Goldberg–Tarjan 1988, p. 930): the number of passes over the queue made by the
first-in, first-out algorithm is at most `4n²`, where `n = |V|`. Pass one consists of the
discharges of the vertices added to the queue during the initialization, and pass `i + 1` of the
discharges of the vertices added during pass `i`; the passes made by the first `K` discharges
number the largest pass tag of a discharged entry. -/
theorem pass_count_le {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (L : V → List V) (K : ℕ) (S : ℕ → State V) (J : ℕ → ℕ)
    (hrun : IsFIFORun N L K S J) :
    passCount K S ≤ 4 * Fintype.card V ^ 2 := by sorry

end GoldbergTarjan.FIFO

