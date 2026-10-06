import Mathlib
import Definitions.Def_AlonMilman_Diameter_lambda1

namespace AlonExpanders.Core

/-- `(n, d, ε)`-enlarger (Alon, *Eigenvalues and expanders*, Combinatorica 6 (1986), §2, p. 85):
a graph on `n` vertices with maximal degree (at most) `d` and `λ(G) ≥ ε`, where `λ(G)` is the
second-smallest eigenvalue of `Q_G = diag(d(v)) − A_G` (`AlonMilman.Diameter.lambda1`). -/
def IsEnlarger {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (n d : ℕ) (ε : ℝ) : Prop :=
  Fintype.card V = n ∧ G.maxDegree ≤ d ∧ ε ≤ AlonMilman.Diameter.lambda1 G

end AlonExpanders.Core
