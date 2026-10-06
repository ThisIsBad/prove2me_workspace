import Mathlib
import Definitions.Def_SecretaryWD_DiscUpper_ClassicalSecretary
import Definitions.Def_SecretaryWD_Graphic_GraphicMatroid

namespace SecretaryWD.Graphic

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The edges of `E` are numbered `0, …, |E| - 1` by a fixed enumeration; `edgeAt E j` is the
edge with number `j`. Arrival orders permute these numbers, and the tie-break prefers the smaller
number among equal values. -/
noncomputable def edgeAt (E : Finset (Sym2 V)) (j : Fin E.card) : Sym2 V :=
  (E.equivFin.symm j).1

/-- The arrival times of the edges of the part `p`, when the edges of `E` arrive in the order
`π` (time `t` brings the edge numbered `π t`). -/
noncomputable def partTimes (E : Finset (Sym2 V)) (π : Equiv.Perm (Fin E.card))
    (p : Finset (Sym2 V)) : Finset (Fin E.card) :=
  Finset.univ.filter fun t => edgeAt E (π t) ∈ p

/-- The time of the `i`-th arrival (0-based) among the edges of the part `p`. -/
noncomputable def partArrivalTime (E : Finset (Sym2 V)) (π : Equiv.Perm (Fin E.card))
    (p : Finset (Sym2 V)) (i : Fin (partTimes E π p).card) : Fin E.card :=
  (partTimes E π p).orderEmbOfFin rfl i

/-- The edge selected in the part `p` (if any): the classical secretary rule run on the arrivals
of the part's edges, in arrival order, ranked by the tie-break key `(v e, edge number)`. -/
noncomputable def partSelection (E : Finset (Sym2 V)) (v : Sym2 V → ℝ)
    (π : Equiv.Perm (Fin E.card)) (p : Finset (Sym2 V)) : Option (Sym2 V) :=
  (SecretaryWD.DiscUpper.classicalSecretary (partTimes E π p).card fun i =>
      SecretaryWD.DiscUpper.tieKey (fun j => v (edgeAt E j)) (π (partArrivalTime E π p i))).map
    fun i => edgeAt E (π (partArrivalTime E π p i))

/-- The output of the per-part algorithm (proof of Theorem 5.4, p. 10) for the partition `P` and
the arrival order `π`: the set of edges selected in the parts. Edges in no part are never
selected. -/
noncomputable def partitionSecretaryOutput (E : Finset (Sym2 V)) (v : Sym2 V → ℝ)
    (P : Finset (Finset (Sym2 V))) (π : Equiv.Perm (Fin E.card)) : Finset (Sym2 V) :=
  P.biUnion fun p => (partSelection E v π p).toFinset

/-- The value of the per-part algorithm's output. -/
noncomputable def partitionSecretaryValue (E : Finset (Sym2 V)) (v : Sym2 V → ℝ)
    (P : Finset (Finset (Sym2 V))) (π : Equiv.Perm (Fin E.card)) : ℝ :=
  ∑ e ∈ partitionSecretaryOutput E v P π, v e

/-- The expected value of the algorithm that draws the partition `P ∼ μ` (independently of the
order), lets the edges of `E` arrive in a uniformly random order, and runs the per-part
algorithm: `E_{P∼μ} E_π [value]`. -/
noncomputable def expectedAlgValue (E : Finset (Sym2 V)) (v : Sym2 V → ℝ)
    (μ : PMF (Finset (Finset (Sym2 V)))) : ℝ :=
  pmfExp μ fun P => SecretaryWD.DiscUpper.uniformAvg fun π => partitionSecretaryValue E v P π

end SecretaryWD.Graphic
