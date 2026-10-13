import Mathlib

namespace WeberGittins.Submodular

/-- The allocations of `t` plays to the bandits of `I`: the maps `m : Fin n → ℕ` (bandit `j`
is played `m j` times) with `m j = 0` for `j ∉ I` and `∑ j, m j = t`. Every such `m` has
`m j ≤ t`, so this finite set is cut out of the box `{0, …, t}ⁿ`. -/
def playAllocations {n : ℕ} (I : Finset (Fin n)) (t : ℕ) : Finset (Fin n → ℕ) :=
  (Fintype.piFinset fun _ : Fin n => Finset.range (t + 1)).filter
    fun m => (∀ j, j ∉ I → m j = 0) ∧ ∑ j, m j = t

lemma playAllocations_nonempty {n : ℕ} {I : Finset (Fin n)} (hI : I ≠ ∅) (t : ℕ) :
    (playAllocations I t).Nonempty := by
  obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 hI
  refine ⟨Pi.single i t, ?_⟩
  simp only [playAllocations, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  refine ⟨fun j => ?_, fun j hj => ?_, ?_⟩
  · by_cases h : j = i
    · subst h; simp
    · simp [h]
  · have : j ≠ i := fun h => hj (h ▸ hi)
    simp [this]
  · simp [Finset.sum_pi_single']

/-- Weber (1992), proof of Theorem 4, p. 1030: `U_t(I)`, the sum of the first `t` elements of the
interleaving into nonincreasing order of the sequences `(H j k)_{k ≥ 0}`, `j ∈ I`.

It is written as the largest total of `t` terms taken as initial segments of the sequences of the
bandits of `I`: `max { ∑_{j ∈ I} ∑_{u < m j} H j u : m ∈ playAllocations I t }`. When every
`H j` is nonincreasing, this maximum is exactly the sum of the first `t` terms of the nonincreasing
interleaving (whatever the tie-breaking). `U_t(∅) = 0`: with no bandit nothing is paid. -/
noncomputable def partialInterleavedSum {n : ℕ} (H : Fin n → ℕ → ℝ) (I : Finset (Fin n))
    (t : ℕ) : ℝ :=
  if hI : I = ∅ then 0 else
    (playAllocations I t).sup' (playAllocations_nonempty hI t)
      fun m => ∑ j ∈ I, ∑ u ∈ Finset.range (m j), H j u

end WeberGittins.Submodular
