import Mathlib
import Definitions.Def_MDPFinance_Stationary_NSValueFunction

open MeasureTheory

namespace MDPFinance.Stationary

/-- Mathlib has no `MeasurableSpace (Matrix m n α)` instance (`Matrix` is a plain, non-reducible
`def` for `m → n → α`); this transports the product `MeasurableSpace` structure across that
definitional equality, needed so a *law* of a random matrix (Bäuerle–Rieder's random transition
coefficients `A_{n+1}, B_{n+1}`, §2.6.3) is a `Measure` on a genuine measurable space. -/
instance instMeasurableSpaceMatrix {m n α : Type*} [MeasurableSpace α] :
    MeasurableSpace (Matrix m n α) :=
  inferInstanceAs (MeasurableSpace (m → n → α))

/-- The quadratic form `x^⊤ Q x` for a square matrix `Q` and a vector `x` (Bäuerle–Rieder use
`x^⊤ Q x` throughout §2.6.3 without a separate numbered definition). -/
def xQx {ι : Type*} [Fintype ι] (Q : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  dotProduct x (Q.mulVec x)

/-- The matrix-valued expectation `𝔼[F(A,B)]`, computed entrywise, of a matrix-valued function
of a jointly-distributed random pair `(A,B) ∼ ν` (Bäuerle–Rieder write `𝔼[A_{n+1}^⊤ Q A_{n+1}]`
etc. throughout §2.6.3 without a separate numbered notation for this expectation operator). -/
noncomputable def jointMatMean {m d : Type*} [Fintype m] [Fintype d] {κ₁ κ₂ : Type*}
    [Fintype κ₁] [Fintype κ₂]
    (ν : Measure (Matrix m m ℝ × Matrix m d ℝ))
    (F : Matrix m m ℝ → Matrix m d ℝ → Matrix κ₁ κ₂ ℝ) : Matrix κ₁ κ₂ ℝ :=
  fun i j => ∫ p, F p.1 p.2 i j ∂ν

end MDPFinance.Stationary
