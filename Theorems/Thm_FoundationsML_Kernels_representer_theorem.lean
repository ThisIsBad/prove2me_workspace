import Mathlib
import Definitions.Def_FoundationsML_Kernels_IsPDS
import Definitions.Def_FoundationsML_Kernels_IsRKHSOf
import Definitions.Def_FoundationsML_Kernels_IsMinimizer

namespace FoundationsML.Kernels

/-- Theorem 6.11 (Representer theorem; goal; Mohri, Rostamizadeh & Talwalkar, *Foundations of
Machine Learning*, 2nd ed., MIT Press 2018, p. 117, PDF p. 134). Let `K : X × X → ℝ` be a PDS
kernel and `H` its corresponding RKHS. Then, for any non-decreasing function `G : ℝ → ℝ` and
any loss function `L : ℝ^m → ℝ ∪ {+∞}`, the optimization problem
`argmin_{h∈H} F(h) = argmin_{h∈H} G(‖h‖_H) + L(h(x_1),…,h(x_m))` admits a solution of the form
`h* = ∑_{i=1}^m α_i K(x_i,·)`. If `G` is further assumed to be increasing, then any solution
has this form.

**Formalization Note.** `L`'s codomain `ℝ ∪ {+∞}` is `WithTop ℝ` (not `EReal`, which would also
admit `-∞`, a harmless-in-the-proof but unstated generalization the book's own display does not
license). `WithTop ℝ` on its own does **not** avoid a different collapse: an unconstrained
`L : (Fin m → ℝ) → WithTop ℝ` may be the constant function `⊤` (legal under the book's own
`ℝ ∪ {+∞}` codomain), which forces `F` to be identically `⊤` and every `h : H` to vacuously
minimize it, including points not of the form `∑ αᵢ • Φ(xᵢ)`; the book's own proof implicitly
assumes the objective's value at *some* point is finite, so `hne` makes that standing assumption
explicit rather than leaving the second conjunct false for `L ≡ ⊤`. `K(x_i,·)` is `Φ (x i)`,
matching Theorem 6.8's own construction (`Φ(x)(x') = K(x,x')`, i.e. `Φ(x)` *is* `K(x,·)`).
Non-decreasing/increasing are `Monotone`/`StrictMono`, matching the book's own two-clause
distinction (existence needs only `Monotone G`; "any solution has this form" needs
`StrictMono G`) exactly. -/
theorem representer_theorem
    {X H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (K : X → X → ℝ) (hK : IsPDS K) (Φ : X → H) (ev : H → X → ℝ)
    (hRKHS : IsRKHSOf K Φ ev)
    (m : ℕ) (x : Fin m → X)
    (G : ℝ → ℝ) (hG : Monotone G)
    (L : (Fin m → ℝ) → WithTop ℝ)
    (F : H → WithTop ℝ) (hF : ∀ h : H, F h = (G ‖h‖ : WithTop ℝ) + L (fun i => ev h (x i)))
    (hne : ∃ h₀ : H, F h₀ ≠ ⊤) :
    (∃ α : Fin m → ℝ, IsMinimizer F (∑ i, α i • Φ (x i))) ∧
    (StrictMono G →
      ∀ h : H, IsMinimizer F h → ∃ α : Fin m → ℝ, h = ∑ i, α i • Φ (x i)) := by sorry

end FoundationsML.Kernels
