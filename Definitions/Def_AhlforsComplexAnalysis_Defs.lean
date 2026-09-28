import Mathlib

namespace AhlforsComplexAnalysis

/-- Ahlfors, *Complex Analysis* (3rd ed.), Ch. 3, §1.3, Definition 4: a *region* is a nonempty,
open, connected subset of the (finite) complex plane. -/
def IsRegion (Ω : Set ℂ) : Prop :=
  IsOpen Ω ∧ IsConnected Ω

/-- Ahlfors, Ch. 4, §4.2, Definition 1: a region is *simply connected* if its
complement with respect to the extended plane `ℂ ∪ {∞}` is connected. -/
def IsSimplyConnectedRegion (Ω : Set ℂ) : Prop :=
  IsRegion Ω ∧ IsConnected (((↑) : ℂ → OnePoint ℂ) '' Ω)ᶜ

/-- Ahlfors, Ch. 5, §5.1, Definition 2 (with values in `S = ℂ`): a family `𝔉` is
*normal in `Ω`* if every sequence of members of `𝔉` has a subsequence converging
uniformly on every compact subset of `Ω`. The limit need not lie in `𝔉`. -/
def IsNormalFamily (𝔉 : Set (ℂ → ℂ)) (Ω : Set ℂ) : Prop :=
  ∀ F : ℕ → ℂ → ℂ, (∀ n, F n ∈ 𝔉) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : ℂ → ℂ,
      ∀ K ⊆ Ω, IsCompact K → TendstoUniformlyOn (fun n => F (φ n)) g Filter.atTop K

end AhlforsComplexAnalysis
