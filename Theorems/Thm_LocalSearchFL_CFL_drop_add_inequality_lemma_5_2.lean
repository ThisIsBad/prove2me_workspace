import Mathlib
import Definitions.Def_LocalSearchFL_CFL_IsCFLLocalOpt

namespace LocalSearchFL.CFL

/-- **Lemma 5.2**, p. 559: in a locally optimum CFL solution `X` (at least one client), for
every set `U` of copies of `X` and every facility `s'`,
`⌈|N_X(U)| / u_{s'}⌉ · f_{s'} + ∑_{s ∈ U} |N_X(s)| · c_{s s'} ≥ ∑_{s ∈ U} f_s`,
where `c_{s s'}` is the distance between the facility of copy `s` and `s'`. -/
theorem drop_add_inequality_lemma_5_2 {Cl Fa : Type} [Fintype Cl] [Nonempty Cl]
    (I : MetricInstance Cl Fa) (u : Fa → ℕ) (hu : ∀ i, 0 < u i) (f : Fa → ℝ) (hf : ∀ i, 0 ≤ f i)
    (X : CFLSol Cl Fa u) (hX : IsCFLLocalOpt I f X) (U : Finset (Fin X.n)) (s' : Fa) :
    ∑ s ∈ U, f (X.loc s) ≤
      (⌈((X.nbhdSet U).card : ℝ) / (u s' : ℝ)⌉₊ : ℝ) * f s' +
        ∑ s ∈ U, ((X.nbhd s).card : ℝ) * I.cf (X.loc s) s' := by sorry

end LocalSearchFL.CFL
