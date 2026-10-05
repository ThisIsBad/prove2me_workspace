import Mathlib
import Definitions.Def_ProcessingNetworks_GlobalStability_QueueingNetworkData

namespace ProcessingNetworks.GlobalStability

/-- A unidirectional ring network (Dai & Harrison p. 152, PDF p. 168), stated as a structural
property of a queueing network: `succ i = some j` means class `i` routes deterministically to
class `j` on completion (`succ i = none` means class `i` exits the network); the ring structure
requires the successor to sit at the very next station (mod `K`); the routes are disjoint paths
(no class is the successor of two classes: each class `(ℓ, j)` belongs to a single customer type
`ℓ` at a single stage `j`), and external arrivals enter only at the first class of a route (a
class with a predecessor has `λ = 0`, since a type-`ℓ` customer enters at the first station of its
route); all classes served at a given station share a common mean service time (`βₖ`); and all
server pools are single-server (`b ≡ 1`). -/
def IsUnidirectionalRing {I K : ℕ} (dat : QueueingNetworkData I K) (succ : Fin I → Option (Fin I)) :
    Prop :=
  (∀ i j : Fin I, dat.P i j = if succ i = some j then 1 else 0) ∧
  (∀ i j : Fin I, succ i = some j → ((dat.p i : ℕ) + 1) % K = (dat.p j : ℕ)) ∧
  (∀ i i' j : Fin I, succ i = some j → succ i' = some j → i = i') ∧
  (∀ i j : Fin I, succ i = some j → dat.lam j = 0) ∧
  (∀ i i' : Fin I, dat.p i = dat.p i' → dat.m i = dat.m i') ∧
  (∀ k : Fin K, dat.b k = 1)

end ProcessingNetworks.GlobalStability
