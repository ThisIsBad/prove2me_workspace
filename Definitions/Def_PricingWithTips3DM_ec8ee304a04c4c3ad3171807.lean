import Definitions.Def_PricingWithTips3DM_10e78846fac3b5dcfc571733
import Definitions.Def_PricingWithTips3DM_a82ad24f6122eea7c40fd2b4
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# General circuit satisfiability is in NP

The executable certificate semantics and the concrete polynomial-time TM2
witness are assembled here into the chapter-level membership theorem.
-/

namespace CLRS.Chapter34

/-- `GeneralCircuitSAT` has polynomial-size assignment certificates checked by
the concrete polynomial-time verifier machine. -/
theorem generalCircuitSAT_polyTimeVerifiable :
    PolyTimeVerifiable GeneralCircuitSAT := by
  refine ⟨generalCircuitVerifier, Polynomial.X, ?_, ?_⟩
  · exact ⟨Turing.GeneralCircuitVerifier.generalCircuitVerifierComputableInPolyTime⟩
  · intro input
    simpa using mem_generalCircuitSAT_iff_exists_certificate input

/-- Public textbook-facing name for polynomial verifiability of general
circuit satisfiability. -/
theorem generalCircuitSAT_verifiable :
    PolyTimeVerifiable GeneralCircuitSAT :=
  generalCircuitSAT_polyTimeVerifiable

/-- The honest serialized general-circuit satisfiability language belongs to
the complexity class `NP`. -/
theorem generalCircuitSAT_mem_ClassNP :
    GeneralCircuitSAT ∈ ClassNP CircuitSym :=
  (mem_ClassNP GeneralCircuitSAT).2 generalCircuitSAT_polyTimeVerifiable

end CLRS.Chapter34
