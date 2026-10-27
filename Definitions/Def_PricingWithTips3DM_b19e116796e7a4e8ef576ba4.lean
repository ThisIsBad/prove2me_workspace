import Definitions.Def_PricingWithTips3DM_a24b63b7f54ee231b2f69f5e
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# General CLIQUE certificate checker

Certificates are duplicate-free vertex lists of exactly the target size.  The
Boolean checker parses both raw strings and checks the typed finite predicate.
-/

namespace CLRS
namespace Chapter34

namespace CliqueInstance

/-- A vertex list is an exact certificate for the requested clique. -/
def ListRepresentsClique (I : CliqueInstance) (vertices : List Nat) : Prop :=
  vertices.Nodup ∧
    vertices.length = I.targetSize ∧
    (∀ v ∈ vertices, v < I.vertexCount) ∧
    ∀ u ∈ vertices, ∀ v ∈ vertices, u ≠ v → I.Adj u v

/-- The finite list certificate predicate is decidable. -/
instance decidableListRepresentsClique (I : CliqueInstance) (vertices : List Nat) :
    Decidable (I.ListRepresentsClique vertices) := by
  unfold ListRepresentsClique
  infer_instance

end CliqueInstance

/-- Total Boolean verifier for a raw certificate and raw CLIQUE instance. -/
def cliqueVerifier (certificate input : List CliqueSym) : Bool :=
  match decodeCliqueInstance input, decodeCliqueCertificate certificate with
  | some I, some vertices =>
      decide (I.WellFormed ∧ I.ListRepresentsClique vertices)
  | _, _ => false

end Chapter34
end CLRS
