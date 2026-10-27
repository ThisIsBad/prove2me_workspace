import Definitions.Def_PricingWithTips_Finset3DM

namespace PricingWithTips

theorem finset3DM_iff_allocation3DM (n : ℕ)
    (T : Finset (ThreeDMTriple n)) :
    HasPerfectFinset3DM n T ↔
      HasPerfect3DMatching n (fun b s d => decide ((b, s, d) ∈ T)) := by
  classical
  constructor
  · rintro ⟨M, hMT, hA, hB, hC⟩
    choose tA htA using hA
    refine ⟨{ assigned := fun b => some (tA b).2, store_unique := ?_, courier_unique := ?_ },
      ?_, ?_⟩
    · intro b₁ b₂ s d₁ d₂ h1 h2
      simp only [Option.some.injEq] at h1 h2
      have u := (hB s).unique ⟨(htA b₁).1.1, by change (tA b₁).2.1 = s; rw [h1]⟩
        ⟨(htA b₂).1.1, by change (tA b₂).2.1 = s; rw [h2]⟩
      calc b₁ = (tA b₁).1 := (htA b₁).1.2.symm
        _ = (tA b₂).1 := by rw [u]
        _ = b₂ := (htA b₂).1.2
    · intro b₁ b₂ s₁ s₂ d h1 h2
      simp only [Option.some.injEq] at h1 h2
      have u := (hC d).unique ⟨(htA b₁).1.1, by change (tA b₁).2.2 = d; rw [h1]⟩
        ⟨(htA b₂).1.1, by change (tA b₂).2.2 = d; rw [h2]⟩
      calc b₁ = (tA b₁).1 := (htA b₁).1.2.symm
        _ = (tA b₂).1 := by rw [u]
        _ = b₂ := (htA b₂).1.2
    · intro b; exact ⟨_, _, rfl⟩
    · intro b s d h
      simp only [Allocation.Trades, Option.some.injEq] at h
      have hm : tA b ∈ T := hMT (htA b).1.1
      have : tA b = (b, s, d) := Prod.ext (htA b).1.2 h
      rw [this] at hm
      simpa using hm
  · rintro ⟨A, hA1, hA2⟩
    choose pr dd hpr using hA1
    let M : Finset (ThreeDMTriple n) := Finset.univ.filter fun t => A.assigned t.1 = some t.2
    have hmem : ∀ t, t ∈ M ↔ A.assigned t.1 = some t.2 := by
      intro t; simp [M]
    have hst_inj : Function.Injective pr := by
      intro b₁ b₂ h
      have h1 : A.assigned b₁ = some (pr b₁, dd b₁) := hpr b₁
      have h2 : A.assigned b₂ = some (pr b₂, dd b₂) := hpr b₂
      rw [h] at h1
      exact A.store_unique h1 h2
    have hco_inj : Function.Injective dd := by
      intro b₁ b₂ h
      have h1 : A.assigned b₁ = some (pr b₁, dd b₁) := hpr b₁
      have h2 : A.assigned b₂ = some (pr b₂, dd b₂) := hpr b₂
      rw [h] at h1
      exact A.courier_unique h1 h2
    have hst_surj := Finite.injective_iff_surjective.mp hst_inj
    have hco_surj := Finite.injective_iff_surjective.mp hco_inj
    refine ⟨M, ?_, ?_, ?_, ?_⟩
    · intro t ht
      rw [hmem] at ht
      have := hA2 t.1 t.2.1 t.2.2 ht
      simpa using this
    · intro b
      refine ⟨(b, pr b, dd b), ⟨(hmem _).mpr (hpr b), rfl⟩, ?_⟩
      rintro ⟨b', s', d'⟩ ⟨ht, hb⟩
      rw [hmem] at ht
      simp only at hb ht
      subst hb
      have hd : A.assigned b' = some (pr b', dd b') := hpr b'
      rw [hd] at ht
      simp only [Option.some.injEq, Prod.mk.injEq] at ht
      rw [ht.1, ht.2]
    · intro s
      obtain ⟨b, hb⟩ := hst_surj s
      refine ⟨(b, pr b, dd b), ⟨(hmem _).mpr (hpr b), hb⟩, ?_⟩
      rintro ⟨b', s', d'⟩ ⟨ht, hs⟩
      rw [hmem] at ht
      simp only at hs ht
      subst hs
      have hd : A.assigned b = some (pr b, dd b) := hpr b
      rw [← hb] at ht
      have hb' := A.store_unique ht hd
      subst hb'
      rw [hd] at ht
      simp only [Option.some.injEq, Prod.mk.injEq] at ht
      rw [ht.2, hb]
    · intro d
      obtain ⟨b, hb⟩ := hco_surj d
      refine ⟨(b, pr b, dd b), ⟨(hmem _).mpr (hpr b), hb⟩, ?_⟩
      rintro ⟨b', s', d'⟩ ⟨ht, hd'⟩
      rw [hmem] at ht
      simp only at hd' ht
      subst hd'
      have hd : A.assigned b = some (pr b, dd b) := hpr b
      rw [← hb] at ht
      have hb' := A.courier_unique ht hd
      subst hb'
      rw [hd] at ht
      simp only [Option.some.injEq, Prod.mk.injEq] at ht
      rw [ht.1, hb]

end PricingWithTips
