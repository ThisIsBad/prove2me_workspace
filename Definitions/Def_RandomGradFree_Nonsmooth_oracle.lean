import Mathlib

namespace RandomGradFree.Nonsmooth

/-- The random gradient-free oracle of Nesterov–Spokoiny, Eq. (30), item 1, already multiplied
by `B⁻¹`: for a direction `u`, `B⁻¹ g_μ(x) = ((f(x + μ u) - f(x)) / μ) • u`. It is only used
with `μ > 0`. -/
noncomputable def oracle {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (μ : ℝ) (x u : E) : E :=
  ((f (x + μ • u) - f x) / μ) • u

end RandomGradFree.Nonsmooth
