import Mathlib
import Definitions.Def_BNCovPack_Routing_Routing
import Definitions.Def_BNCovPack_Routing_FracScheme
import Definitions.Def_BNCovPack_Routing_Potential

namespace BNCovPack.Routing

/-- State of the integral online routing algorithm of §5.2 (pp. 15–16): the fractional scheme's
state, the integral edge usage `chi e = χ(e)` (number of chosen paths that use `e`) and the
number `served = ∑_{r_i} χ(r_i)` of requests served so far. -/
structure State (E : Type*) where
  frac : FracState E
  chi : E → ℕ
  served : ℕ

/-- The initial state: all-zero fractional state, no edge used, no request served. -/
def State.init (E : Type*) : State E where
  frac := FracState.init E
  chi := fun _ => 0
  served := 0

/-- Serving a request on path `P` adds one to `χ(e)` for every `e ∈ P`. -/
def addPath {E : Type*} [DecidableEq E] (chi : E → ℕ) (P : Finset E) : E → ℕ :=
  fun e => chi e + if e ∈ P then 1 else 0

open Classical in
/-- One round of the algorithm (p. 15) on arrival of request `r_i` with path list `ps = P(r_i)`:
1. the fractional scheme `fracStep` raises the flows of `r_i`; `fs` is the list of flows
   `f(r_i, P)` it gave to the paths of `ps` (the last entry of the new `flows`);
2. with `Φ^start` the potential before the flows were raised, the request is served on the
   first flow path `P` of `ps` (in list order: a path whose flow `f(r_i, P)` is positive) such
   that serving it on `P` gives potential `≤ Φ^start`, computed with the new flows;
3. if there is no such path the request is rejected (`χ` unchanged); in particular a request
   whose flow was not increased is rejected.
The total flow is `routingValue` of the flows and the loads are the fractional state's loads. -/
noncomputable def step {E : Type*} [Fintype E] [DecidableEq E] (u : E → ℝ) (ℓ : ℕ)
    (Bf B : ℝ) (st : State E) (ps : List (Finset E)) : State E :=
  let fr' := fracStep u ℓ Bf st.frac ps
  let Φstart := potential u B (routingValue st.frac.flows) st.frac.load st.chi st.served
  let fs := fr'.flows.getLastD []
  let good : Finset E × ℝ → Bool := fun Py =>
    decide (0 < Py.2) &&
      decide (potential u B (routingValue fr'.flows) fr'.load (addPath st.chi Py.1)
        (st.served + 1) ≤ Φstart)
  match (ps.zip fs).find? good with
  | some Py => { frac := fr', chi := addPath st.chi Py.1, served := st.served + 1 }
  | none => { frac := fr', chi := st.chi, served := st.served }

/-- The state of the algorithm with fractional parameters `ℓ`, `Bf` and rounding scale `B` after
the requests of `σ` have arrived, in order. -/
noncomputable def run {E : Type*} [Fintype E] [DecidableEq E] (u : E → ℝ) (ℓ : ℕ) (Bf B : ℝ)
    (σ : List (List (Finset E))) : State E :=
  σ.foldl (step u ℓ Bf B) (State.init E)

/-- The algorithm of §5.2 with the paper's parameters, for path systems whose paths have at most
`Pmax` edges: the fractional scheme with `ℓ = Pmax + 1` (a primal constraint has support `P` and
`Z(r_i)`) and `B' = 2 ln(1 + ℓ) = 2 ln(Pmax + 2)`, and the rounding scale
`B = exp(1 + ln(2m)/u(min)) − 1`. -/
noncomputable def algorithm {E : Type*} [Fintype E] [Nonempty E] [DecidableEq E] (u : E → ℝ)
    (Pmax : ℕ) (σ : List (List (Finset E))) : State E :=
  run u (Pmax + 1) (2 * Real.log ((Pmax : ℝ) + 2)) (roundingScale u) σ

end BNCovPack.Routing
