import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P07
import Definitions.Def_QAlgorithms_Defs_SDP

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace MassiveChannels.GCE

open QAlgorithms
open QAlgorithms.Papers.Independent.Dependency50.P07

/-- The grand-canonical density matrix at inverse temperature `beta` and chemical potential `mu`. -/
def rhoGCE {Q : Type} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    (Ham Nop : Matrix Q Q ℂ) (beta mu : ℝ) : Matrix Q Q ℂ :=
  gibbsState ((-(beta : ℂ)) • (Ham - (mu : ℂ) • Nop))

/-- Expectation of an observable in a state, taking the real trace. -/
def expect {Q : Type} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    (A rho : Matrix Q Q ℂ) : ℝ :=
  (rho * A).trace.re

/-- Both average constraints are exact equalities for an arbitrary finite ensemble. -/
def Admissible {X Q : Type} [Fintype X] [Fintype Q] [DecidableEq Q] [Nonempty Q]
    (Ham Nop : Matrix Q Q ℂ) (E N : ℝ) (e : CQData X Q) : Prop :=
  e.Valid ∧ expect Ham (ensembleMean e) = E ∧ expect Nop (ensembleMean e) = N

/-- Accessible-information values of every finite admissible ensemble, including mixed states. -/
def capacityValues {Q : Type} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    (Ham Nop : Matrix Q Q ℂ) (E N : ℝ) : Set ℝ :=
  {v | ∃ (k : ℕ) (e : CQData (Fin k) Q),
    Admissible Ham Nop E N e ∧ v = accessibleInformation e}

/-- An orthonormal basis whose vectors are eigenvectors of both physical observables. -/
def IsJointEigenbasis {Q : Type} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    (Ham Nop : Matrix Q Q ℂ)
    (v : OrthonormalBasis Q ℂ (EuclideanSpace ℂ Q)) : Prop :=
  ∀ j : Q, ∃ a b : ℝ,
    (∀ i : Q, (∑ k : Q, Ham i k * v j k) = (a : ℂ) * v j i) ∧
    (∀ i : Q, (∑ k : Q, Nop i k * v j k) = (b : ℂ) * v j i)

/-- The ensemble of pure basis states with the Born weights of `rho`. -/
def fockEnsemble {Q : Type} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    (rho : Matrix Q Q ℂ)
    (v : OrthonormalBasis Q ℂ (EuclideanSpace ℂ Q)) : CQData Q Q where
  prob j := effectProb (pureDensity (v j)) rho
  state j := pureDensity (v j)

end MassiveChannels.GCE
