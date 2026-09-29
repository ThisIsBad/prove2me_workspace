import Mathlib
import Definitions.Def_ArrowDebreu_Shared_AbstractEconomy
open ArrowDebreu.Shared

namespace ArrowDebreu.ThmI

open AbstractEconomy

/-- **Lemma (§2.5)**, Arrow & Debreu, Econometrica 22 (1954), p. 274 (PDF p. 11): if, for each
`ι`, `𝔄_ι` is compact and convex, `f_ι(ā_ι, a_ι)` is continuous on `𝔄` and quasi-concave in `a_ι`
for every `ā_ι`, `A_ι(ā_ι)` is a continuous function whose graph is a closed set, and, for every
`ā_ι`, the set `A_ι(ā_ι)` is convex and non-empty, then the abstract economy has an equilibrium
point. (The paper proves it by citing Debreu, PNAS 38 (1952), p. 888, and its Remark, p. 889.)

**Formalization Note.**
* The players form a finite type `ι` (the paper's `ι = 1, ⋯, ν`); all action sets lie in `R^l`.
* "Continuous" is §2.4's sequential definition (lower hemicontinuity) at every `ā_ι ∈ 𝔄̄_ι`
  (`ConstrContinuous`); "graph closed" is closedness of `{a | ā_ι ∈ 𝔄̄_ι, a_ι ∈ A_ι(ā_ι)}` in
  `(R^l)^ι`.
* "for every `ā_ι`" ranges over `𝔄̄_ι = Π_{κ ≠ ι} 𝔄_κ` (`OthersIn`); the own coordinate of the
  profile is irrelevant (`constr_indep`), and for the pay-off it is replaced via `Function.update`.
* **Added hypothesis** `∀ ι, 𝔄_ι ≠ ∅`. The paper leaves it implicit (Debreu's action sets are
  contractible polyhedra, hence nonempty). Without it the Lemma is false for `ν ≥ 2`: if every
  `𝔄_ι` is empty, every `𝔄̄_ι` is empty, all other hypotheses hold vacuously, and `𝔄 = ∅` has no
  point. With `ν = 1` the nonemptiness of `A_1` already forces it. -/
theorem lemma_2_5 {ι : Type*} [Fintype ι] [DecidableEq ι] {l : ℕ} (G : AbstractEconomy ι l)
    (hne : ∀ i, (G.act i).Nonempty)
    (hcpt : ∀ i, IsCompact (G.act i)) (hconv : ∀ i, Convex ℝ (G.act i))
    (hcont : ∀ i, ContinuousOn (G.payoff i) G.profiles)
    (hqc : ∀ i a, G.OthersIn i a →
      QuasiconcaveOn ℝ (G.act i) (fun b => G.payoff i (Function.update a i b)))
    (hAcont : ∀ i, G.ConstrContinuous i)
    (hAgraph : ∀ i, IsClosed (G.graph i))
    (hAconv : ∀ i a, G.OthersIn i a → Convex ℝ (G.constr i a))
    (hAne : ∀ i a, G.OthersIn i a → (G.constr i a).Nonempty) :
    ∃ a, G.IsEquilibriumPoint a := by sorry

end ArrowDebreu.ThmI
