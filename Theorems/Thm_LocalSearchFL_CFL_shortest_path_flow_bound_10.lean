import Mathlib
import Definitions.Def_LocalSearchFL_CFL_IsCFLLocalOpt

namespace LocalSearchFL.CFL

/-- **Inequality (10)**, p. 560: for any two CFL solutions `X` and `O` (with `O` opening at
least one copy), route the flow of every `v_s` along a shortest path `v_s → w_{τ(s)} → sink`,
i.e. `τ(s)` minimizes `c_{so} + f_o/u_o` over the copies `o` of `O` (ties broken arbitrarily);
writing `T_o = τ⁻¹(o)`, this flow satisfies
`cost_s(X) + cost_s(O) + cost_f(O) ≥ ∑_{o ∈ O} ∑_{s ∈ T_o} |N_X(s)| (c_{so} + f_o/u_o)`. -/
theorem shortest_path_flow_bound_10 {Cl Fa : Type} [Fintype Cl]
    (I : MetricInstance Cl Fa) (u : Fa → ℕ) (hu : ∀ i, 0 < u i) (f : Fa → ℝ) (hf : ∀ i, 0 ≤ f i)
    (X O : CFLSol Cl Fa u) (hO : 0 < O.n) :
    ∃ τ : Fin X.n → Fin O.n,
      (∀ s o, I.cf (X.loc s) (O.loc (τ s)) + f (O.loc (τ s)) / (u (O.loc (τ s)) : ℝ) ≤
        I.cf (X.loc s) (O.loc o) + f (O.loc o) / (u (O.loc o) : ℝ)) ∧
      ∑ o, ∑ s ∈ Finset.univ.filter (fun s => τ s = o),
          ((X.nbhd s).card : ℝ) * (I.cf (X.loc s) (O.loc o) + f (O.loc o) / (u (O.loc o) : ℝ)) ≤
        costS I X + costS I O + costF f O := by sorry

end LocalSearchFL.CFL
