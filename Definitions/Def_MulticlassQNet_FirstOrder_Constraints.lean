import Mathlib
import Definitions.Def_MulticlassQNet_FirstOrder_Network

namespace MulticlassQNet.FirstOrder

namespace Network

variable {N R : ℕ} (net : Network N R)

/-- Restriction (17) on the f-parameters `f` for the class set `S`, with station values `fi`:
for every `r ∈ S`, `μ_r [∑_{r'∈S} p_{rr'}(f(r) - f(r')) + ∑_{r'∉S} p_{rr'} f(r)] = f_{σ(r)}`,
where the sum over `r' ∉ S` includes the exit `r' = 0`; every `f_i ≥ 0`; and `f_i = 0` when
`C_i ∩ S = ∅`. -/
def FCondition (S : Finset (Fin R)) (f : Fin R → ℝ) (fi : Fin N → ℝ) : Prop :=
  (∀ r ∈ S, net.μ r * (∑ r' ∈ S, net.p r r' * (f r - f r') +
      (∑ r' ∈ Sᶜ, net.p r r' + net.exitProb r) * f r) = fi (net.σ r)) ∧
  (∀ i, 0 ≤ fi i) ∧
  (∀ i, (∀ r ∈ S, net.σ r ≠ i) → fi i = 0)

/-- The numerator `N'(S)` of (18); the sums over `r' ∉ S` include the exit `r' = 0`. -/
def Nprime (lam : Fin R → ℝ) (S : Finset (Fin R)) (f : Fin R → ℝ) : ℝ :=
  ∑ r ∈ S, net.lam0 r * f r ^ 2 +
  ∑ r ∈ Sᶜ, lam r * ∑ r' ∈ S, net.p r r' * f r' ^ 2 +
  ∑ r ∈ S, lam r * (∑ r' ∈ S, net.p r r' * (f r - f r') ^ 2 +
      (∑ r' ∈ Sᶜ, net.p r r' + net.exitProb r) * f r ^ 2)

/-- The denominator `D'(S) = 2 [∑_{i=1}^N f_i - ∑_{r∈S} λ_{0r} f(r)]` of (18). -/
def Dprime (S : Finset (Fin R)) (f : Fin R → ℝ) (fi : Fin N → ℝ) : ℝ :=
  2 * (∑ i, fi i - ∑ r ∈ S, net.lam0 r * f r)

/-- Equalities (24) of Theorem 4.2, in the variables `n r` (for `λ_r x_r`) and `I r r'`. -/
def Eq24 (lam n : Fin R → ℝ) (I : Fin R → Fin R → ℝ) : Prop :=
  ∀ r, 2 * net.μ r * I r r - 2 * ∑ r', net.μ r' * net.p r' r * I r' r
      - 2 * net.lam0 r * n r
    = net.lam0 r + lam r * (1 - net.p r r) + ∑ r' ∈ Finset.univ.erase r, lam r' * net.p r' r

/-- Equalities (25) of Theorem 4.2, for all classes `r' < r`. -/
def Eq25 (lam n : Fin R → ℝ) (I : Fin R → Fin R → ℝ) : Prop :=
  ∀ r r', r' < r →
    net.μ r * I r r' + net.μ r' * I r' r - ∑ w, net.μ w * net.p w r * I w r'
      - ∑ w, net.μ w * net.p w r' * I w r - net.lam0 r * n r' - net.lam0 r' * n r
    = -(lam r * net.p r r') - lam r' * net.p r' r

/-- Equalities (28) of Theorem 4.3, in the variables `n`, `I` and `Nv i r'` (for `N_{ir'}`). -/
def Eq28 (n : Fin R → ℝ) (I : Fin R → Fin R → ℝ) (Nv : Fin N → Fin R → ℝ) : Prop :=
  ∀ i r', ∑ r ∈ net.C i, I r r' + Nv i r' = n r'

end Network

end MulticlassQNet.FirstOrder
