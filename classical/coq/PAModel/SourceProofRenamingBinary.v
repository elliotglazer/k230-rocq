From PAModel Require Import Model NumericalContexts NumericalEnvironments NumericalContextRenaming
  NumericalRenaming NumericalTraces SourcePropositionalRules SourceQuantifierRules SourceSequents
  NumericalSourceFull SourceRenamingWellformedness SetFormulaCodes SourceProofRenamingInvariant.
Unset Implicit Arguments.

Theorem source_proof_renaming_prop_binary M r p q :
  source_proof_renaming_invariant M p -> source_proof_renaming_invariant M q ->
  source_prop_binary M r p q -> source_proof_renaming_invariant M r.
Proof.
  intros HP HQ HRule. assert (HO:source_full_row M r).
  { apply (trace_derives_binary M source_full_rules r p q (proj1 HP) (proj1 HQ)).
    apply source_full_trace_binary. now left. }
  destruct HRule as [_ [H|[H|[H|H]]]].
  - destruct H as (b & c & n & a & d & f & HR & HS & HT & HF).
    apply (source_proof_renaming_ordinary_intro M r b c n d HO HR).
    intros rb rc rn delta ub uc dr HC HD.
    destruct (numerical_renaming_total M a rb rc rn delta) as [ar HA].
    destruct (numerical_renaming_total M f rb rc rn delta) as [fr HFR].
    apply (full_source_IE M ub uc n ar dr fr).
    + exact (source_proof_renaming_target_wf M r b c n d rb rc rn delta ub uc dr HO HR HC HD).
    + exact (proj1 (proj2 HP) b c n f rb rc rn delta ub uc fr HS HC HFR).
    + exact (proj1 (proj2 HQ) b c n a rb rc rn delta ub uc ar HT HC HA).
    + exact (source_binary_renaming_graph M SFImpl a d f rb rc rn delta ar dr fr (or_intror (or_intror eq_refl)) HF HA HD HFR).
  - destruct H as (b & c & n & a & d & f & HR & HS & HT & HF).
    apply (source_proof_renaming_ordinary_intro M r b c n f HO HR).
    intros rb rc rn delta ub uc fr HC HFR.
    destruct (numerical_renaming_total M a rb rc rn delta) as [ar HA].
    destruct (numerical_renaming_total M d rb rc rn delta) as [dr HD].
    apply (full_source_CI M ub uc n ar dr fr).
    + exact (source_proof_renaming_target_wf M r b c n f rb rc rn delta ub uc fr HO HR HC HFR).
    + exact (proj1 (proj2 HP) b c n a rb rc rn delta ub uc ar HS HC HA).
    + exact (proj1 (proj2 HQ) b c n d rb rc rn delta ub uc dr HT HC HD).
    + exact (source_binary_renaming_graph M SFAnd a d f rb rc rn delta ar dr fr (or_introl eq_refl) HF HA HD HFR).
  - destruct H as (b & c & n & a & d & f & sb & sc & sn & tb & tc & tn & HR & HS & HT & HConsA & HConsD).
    apply (source_proof_renaming_branch_intro M r b c n a d f HO HR).
    intros rb rc rn delta ub uc ar dr fr HC HA HD HFR.
    destruct (environment_cons_total M ub uc n ar) as [ab [ac [an HNewA]]].
    destruct (environment_cons_total M ub uc n dr) as [db [dc [dn HNewD]]].
    assert (ENA:an=sn) by (rewrite (proj1 HNewA);symmetry;exact (proj1 HConsA)). subst an.
    assert (END:dn=tn) by (rewrite (proj1 HNewD);symmetry;exact (proj1 HConsD)). subst dn.
    apply (full_source_BranchPair M ub uc n ar dr fr ab ac sn db dc tn).
    + apply (source_renaming_branches_wf M b c n a d f rb rc rn delta ub uc ar dr fr);try assumption.
      exact (source_branches_wf_from_row M b c n a d f r HR (source_full_row_wellformed M r HO)).
    + apply (proj1 (proj2 HP) sb sc sn f rb rc rn delta ab ac fr HS);[|exact HFR].
      exact (context_renaming_cons M b c n rb rc rn delta ub uc a ar sb sc sn ab ac HC HA HConsA HNewA).
    + apply (proj1 (proj2 HQ) tb tc tn f rb rc rn delta db dc fr HT);[|exact HFR].
      exact (context_renaming_cons M b c n rb rc rn delta ub uc d dr tb tc tn db dc HC HD HConsD HNewD).
    + exact HNewA.
    + exact HNewD.
  - destruct H as (b & c & n & a & d & f & disj & HR & HS & HT & HF).
    apply (source_proof_renaming_ordinary_intro M r b c n f HO HR).
    intros rb rc rn delta ub uc fr HC HFR.
    destruct (numerical_renaming_total M a rb rc rn delta) as [ar HA].
    destruct (numerical_renaming_total M d rb rc rn delta) as [dr HD].
    destruct (numerical_renaming_total M disj rb rc rn delta) as [disjr HDisj].
    apply (full_source_DE M ub uc n ar dr fr disjr).
    + exact (source_proof_renaming_target_wf M r b c n f rb rc rn delta ub uc fr HO HR HC HFR).
    + exact (proj1 (proj2 HP) b c n disj rb rc rn delta ub uc disjr HS HC HDisj).
    + exact (proj2 (proj2 HQ) b c n a d f rb rc rn delta ub uc ar dr fr HT HC HA HD HFR).
    + exact (source_binary_renaming_graph M SFOr a d disj rb rc rn delta ar dr disjr
        (or_intror (or_introl eq_refl)) HF HA HD HDisj).
Qed.

Print Assumptions source_proof_renaming_prop_binary.
