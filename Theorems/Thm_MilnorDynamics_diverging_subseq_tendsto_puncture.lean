import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

theorem diverging_subseq_tendsto_puncture (U : Set ℂ) (hU : IsOpen U) (hUc : IsConnected U)
    (f : ℕ → ℂ → ℂ)
    (hf : ∀ n, DifferentiableOn ℂ (f n) U ∧ MapsTo (f n) U ({0, 1}ᶜ : Set ℂ))
    (hdiv : DivergesLocallyUniformlyFrom f U ({0, 1}ᶜ : Set ℂ)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ c ∈ ({((0 : ℂ) : OnePoint ℂ), ((1 : ℂ) : OnePoint ℂ), ∞} : Set (OnePoint ℂ)),
        TendstoLocallyUniformlyOnSphere (fun n z => ((f (φ n) z : ℂ) : OnePoint ℂ))
          (fun _ => c) U := by sorry

end MilnorDynamics
