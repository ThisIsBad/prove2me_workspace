import Definitions.Def_PricingWithTips3DM_bbaac3743d036b03526ad1a7Part2Chunk2
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- The compact one-hot invocation payload never contains the outer row
boundary symbol. -/
theorem affineExactlyOneOutputInvocationFamily_no_frameEnd
    (frames : List AffineExactlyOneFrame) :
    ∀ symbol ∈ encodeAffineExactlyOneOutputSourceInvocationFamily frames,
      symbol ≠ UnaryFrameSym.frameEnd := by
  intro symbol hsymbol
  rw [encodeAffineExactlyOneOutputSourceInvocationFamily,
    List.mem_flatMap] at hsymbol
  rcases hsymbol with ⟨frame, hframe, hsymbol⟩
  rw [encodeAffineExactlyOneOutputSourceInvocation, encodeUnaryFrame,
    List.mem_flatMap] at hsymbol
  rcases hsymbol with ⟨value, hvalue, hsymbol⟩
  simp [encodeUnaryFrameBlock] at hsymbol
  rcases hsymbol with ⟨_, rfl⟩ | rfl <;> simp
end CLRS.Chapter34.Turing.CookLevin
