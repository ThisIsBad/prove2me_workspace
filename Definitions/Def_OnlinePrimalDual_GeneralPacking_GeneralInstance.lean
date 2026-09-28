import Mathlib

namespace OnlinePrimalDual.GeneralPacking

/-- The general packing-covering instance data (Buchbinder & Naor, FnT TCS 2009, Section 14,
p. 246-247, Fig. 14.1): a finite set `I` of primal (covering) variables with positive cost
coefficients `c`, and a finite set `J` of dual (packing) variables/covering constraints, each
pair `(i, j)` carrying a non-negative coefficient `a(i,j)` — the generalization of Chapter 4's
framework from `a(i,j) ∈ {0,1}` to arbitrary non-negative reals. -/
structure GeneralInstance (I J : Type*) [Fintype I] [Fintype J] where
  /-- `a i j` is the (non-negative) coefficient of primal variable `i` in constraint `j`. -/
  a : I → J → ℝ
  ha_nonneg : ∀ i j, 0 ≤ a i j
  /-- The (positive) cost coefficients of the covering objective. -/
  c : I → ℝ
  hc_pos : ∀ i, 0 < c i

end OnlinePrimalDual.GeneralPacking
