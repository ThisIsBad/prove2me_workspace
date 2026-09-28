import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_SymmetricSetFun
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_NonmonotoneSubmod_Shared_F

namespace NonmonotoneSubmod.RandomSet

/-- Theorem 2.1 (Feige–Mirrokni–Vondrák 2011, p. 1137). Let `f : 2^X → ℝ₊` be a nonnegative
submodular function on a finite ground set `X`, let `OPT = max_{S ⊆ X} f(S)`, and let
`R = X(1/2)` be a uniformly random subset of `X`. Then `E[f(R)] ≥ ¼ OPT`; if in addition `f` is
symmetric (`f(X \ S) = f(S)` for every `S`), then `E[f(R)] ≥ ½ OPT`. -/
theorem random_set_approx {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f) :
    (1 / 4) * NonmonotoneSubmod.Shared.OPT f ≤ NonmonotoneSubmod.Shared.F f (fun _ => 1 / 2) ∧
      (NonmonotoneSubmod.Shared.SymmetricSetFun f → (1 / 2) * NonmonotoneSubmod.Shared.OPT f ≤ NonmonotoneSubmod.Shared.F f (fun _ => 1 / 2)) := by sorry

end NonmonotoneSubmod.RandomSet

