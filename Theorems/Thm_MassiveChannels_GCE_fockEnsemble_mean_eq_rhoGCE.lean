import Mathlib
import Definitions.Def_MassiveChannels_GCE_Model

set_option autoImplicit false

noncomputable section

namespace MassiveChannels.GCE

open QAlgorithms
open QAlgorithms.Papers.Independent.Dependency50.P07

/-- A joint eigenbasis of `Ham` and `Nop` exists, and for every such basis the GCE is the
average of its pure, orthogonal basis (Fock) states with the Born weights. -/
theorem fockEnsemble_mean_eq_rhoGCE {Q : Type} [Fintype Q] [DecidableEq Q]
    [Nonempty Q] (Ham Nop : Matrix Q Q ℂ) (hH : Ham.IsHermitian)
    (hN : Nop.IsHermitian) (hcomm : Ham * Nop = Nop * Ham) (beta mu : ℝ) :
    (∃ v : OrthonormalBasis Q ℂ (EuclideanSpace ℂ Q), IsJointEigenbasis Ham Nop v) ∧
    ∀ v : OrthonormalBasis Q ℂ (EuclideanSpace ℂ Q), IsJointEigenbasis Ham Nop v →
      (fockEnsemble (rhoGCE Ham Nop beta mu) v).Valid ∧
      ensembleMean (fockEnsemble (rhoGCE Ham Nop beta mu) v) =
        rhoGCE Ham Nop beta mu := by sorry

end MassiveChannels.GCE

