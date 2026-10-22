import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core
import Definitions.Def_FoundationsRL_RLBasics_UCBVI
import Definitions.Def_FoundationsRL_FuncApprox_Core
import Definitions.Def_FoundationsRL_FuncApprox_BiLinUCB
import Definitions.Def_FoundationsRL_FuncApprox_Normalization


namespace FoundationsRL.FuncApprox

open FoundationsRL.RLBasics

/-- **Lemma 29** (Foster–Rakhlin, arXiv:2312.16730v1, p. 142, Lemma 29), under the standing
assumptions of Section 7: rewards normalized (`RewardsNormalized M`: per-step rewards in
`[0,1]` and `Σ_h r_h ≤ 1` along every trajectory of positive probability), a `[0,1]`-valued
value-function class (`IsNormalizedValueClass`) with `Q^{M⋆,⋆} ∈ 𝒬` (encoded by `q0`) and at
least two members. For any `δ > 0`, if `β = c · (K·log|𝒬| + log(HK/δ)) / n` for a sufficiently
large absolute constant `c`, then with probability at least `1 - δ` over BiLinUCB's `K·n`
episodes, simultaneously for all iterations `k ∈ [K]`: (1) every `Q` retained in the
confidence set `𝒬_k` has, at every layer, its true Bellman residual along the played policies
`π_1,…,π_{k-1}` summing in square to at most an absolute constant `C` times `β` (Eq. (7.27));
(2) `Q^{M⋆,⋆} ∈ 𝒬_k`.

Corrected replacement of `confidence_set_validity`: the retired statement omitted the
Section 7 reward normalization and the `[0,1]` range of the class, so rescaling the rewards
pushed the empirical residual of `Q^⋆` above `β`. The hypothesis `1 < |𝒬|` corrects the printed
statement, which is false for `|𝒬| = 1`: then `β = c·log(HK/δ)/n` while
`Σ_{i<k} (Ê^i_h(Q^⋆))² ≈ k·Var/n` grows linearly in `k` (the printed proof drops the factor `k`
when summing (7.28) over `i < k`); for `|𝒬| ≥ 2` the term `K·log|𝒬| ≥ K·log 2` restores the
claim. The superfluous `δ ≤ 1` is dropped. -/
theorem confidence_set_validity_v2 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {S A : Type} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A]
        {H : ℕ} (M : EpisodicMDP S A H) (_hM : RewardsNormalized M)
        {Qc : Type} [Fintype Qc] [Nonempty Qc] (_hQc : 1 < Fintype.card Qc)
        (qeval : Qc → ℕ → S → A → ℝ) (_hQ : IsNormalizedValueClass H qeval) (q0 : Qc)
        (_hq0 : qeval q0 = fun h s a => if h < H then Qstar M h s a else 0)
        (n K : ℕ) (δ : ℝ), 0 < n → 0 < δ →
        ∀ β : ℝ, β = c * ((K : ℝ) * Real.log (Fintype.card Qc) + Real.log ((H : ℝ) * K / δ)) / n →
        probEvent M (biLinUCBLearner M qeval n β) (K * n)
            (fun histT =>
              ∀ k, k < K →
                (∀ Qf ∈ confSet M qeval (List.ofFn histT) n β k, ∀ h : Fin H,
                    ∑ i ∈ Finset.range k,
                      (bellmanResidual M (iterPolicy M qeval (List.ofFn histT) n β i) h.1
                        (qeval Qf)) ^ 2 ≤ C * β) ∧
                q0 ∈ confSet M qeval (List.ofFn histT) n β k)
          ≥ 1 - δ := by sorry

end FoundationsRL.FuncApprox
