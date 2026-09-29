import Mathlib
import Definitions.Def_GravesWillems_Serial_backlog

namespace GravesWillems.Serial

/-- Eq. (A2) of Graves–Willems 2000 (Appendix, p. 81): the backlog defined by the recursion (A1)
has the closed max-form
`Qᵢ(t) = max[0, max_{i ≤ j ≤ N} (d(t − Tᵢ − ⋯ − T_j, t] − Bᵢ − ⋯ − B_j)]` for `i = 1, …, N`. -/
theorem backlog_closed_form (N : ℕ) (T : ℕ → ℕ) (B : ℕ → ℝ) (d : ℤ → ℝ) (i : ℕ)
    (hi : i ∈ Finset.Icc 1 N) (t : ℤ) :
    backlog N T B d i t =
      max 0 ((Finset.Icc i N).sup' (Finset.nonempty_Icc.mpr (Finset.mem_Icc.mp hi).2)
        (fun j => windowDemand d (t - ((∑ m ∈ Finset.Icc i j, T m : ℕ) : ℤ)) t
          - ∑ m ∈ Finset.Icc i j, B m)) := by sorry

end GravesWillems.Serial
