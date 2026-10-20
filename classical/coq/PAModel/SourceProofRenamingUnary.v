From PAModel Require Import Model CodeExpressions NumericalContexts NumericalEnvironments
  NumericalContextRenaming NumericalRenaming NumericalTraces SourcePropositionalRules
  SourceQuantifierRules SourceSequents NumericalSourceFull SetFormulaCodes SourceProofRenamingInvariant.
Unset Implicit Arguments.

Theorem source_proof_renaming_base M r : source_prop_base M r -> source_proof_renaming_invariant M r.
Proof.
  intro HRule. assert (HO:source_full_row M r).
  { apply trace_derives_base. apply source_full_trace_base. exact HRule. }
  destruct HRule as [_ [H|H]].
  - destruct H as (b & c & n & f & HR & HF).
    apply (source_proof_renaming_ordinary_intro M r b c n f HO HR).
    intros rb rc rn delta ub uc fr HC HFR.
    apply full_source_Ctx.
    + exact (source_proof_renaming_target_wf M r b c n f rb rc rn delta ub uc fr HO HR HC HFR).
    + destruct (context_renaming_member_forward M b c n rb rc rn delta ub uc f HC HF) as [g [HG HRG]].
      pose proof (numerical_renaming_functional M f rb rc rn delta g fr HRG HFR) as E. now subst g.
  - destruct H as (b & c & n & a & d & x & y & f & HR & HX & HY & HF).
    apply (source_proof_renaming_ordinary_intro M r b c n f HO HR).
    intros rb rc rn delta ub uc fr HC HFR.
    destruct (numerical_renaming_total M a rb rc rn delta) as [ar HA].
    destruct (numerical_renaming_total M d rb rc rn delta) as [dr HD].
    destruct (numerical_renaming_total M x rb rc rn delta) as [xr HXR].
    destruct (numerical_renaming_total M y rb rc rn delta) as [yr HYR].
    apply (full_source_Pc M ub uc n ar dr xr yr fr).
    + exact (source_proof_renaming_target_wf M r b c n f rb rc rn delta ub uc fr HO HR HC HFR).
    + exact (source_binary_renaming_graph M SFImpl a d x rb rc rn delta ar dr xr (or_intror (or_intror eq_refl)) HX HA HD HXR).
    + exact (source_binary_renaming_graph M SFImpl x a y rb rc rn delta xr ar yr (or_intror (or_intror eq_refl)) HY HXR HA HYR).
    + exact (source_binary_renaming_graph M SFImpl y a f rb rc rn delta yr ar fr (or_intror (or_intror eq_refl)) HF HYR HA HFR).
Qed.

Theorem source_proof_renaming_prop_unary M r p :
  source_proof_renaming_invariant M p -> source_prop_unary M r p -> source_proof_renaming_invariant M r.
Proof.
  intros HP HRule. assert (HO:source_full_row M r).
  { apply (trace_derives_unary M source_full_rules r p (proj1 HP)). apply source_full_trace_unary. now left. }
  destruct HRule as [_ [H|[H|[H|[H|[H|H]]]]]].
  - destruct H as (b & c & n & a & d & f & sb & sc & sn & HR & HS & HCons & HF).
    apply (source_proof_renaming_ordinary_intro M r b c n f HO HR).
    intros rb rc rn delta ub uc fr HC HFR.
    destruct (numerical_renaming_total M a rb rc rn delta) as [ar HA].
    destruct (numerical_renaming_total M d rb rc rn delta) as [dr HD].
    destruct (environment_cons_total M ub uc n ar) as [vb [vc [vn HNew]]].
    assert (EN:vn=sn) by (rewrite (proj1 HNew);symmetry;exact (proj1 HCons)). subst vn.
    apply (full_source_II M ub uc n ar dr fr vb vc sn).
    + exact (source_proof_renaming_target_wf M r b c n f rb rc rn delta ub uc fr HO HR HC HFR).
    + apply (proj1 (proj2 HP) sb sc sn d rb rc rn delta vb vc dr HS);[|exact HD].
      exact (context_renaming_cons M b c n rb rc rn delta ub uc a ar sb sc sn vb vc HC HA HCons HNew).
    + exact HNew.
    + exact (source_binary_renaming_graph M SFImpl a d f rb rc rn delta ar dr fr
        (or_intror (or_intror eq_refl)) HF HA HD HFR).
  - destruct H as (b & c & n & f & HR & HS).
    apply (source_proof_renaming_ordinary_intro M r b c n f HO HR).
    intros rb rc rn delta ub uc fr HC HFR. apply (full_source_Exp M ub uc n fr).
    + exact (source_proof_renaming_target_wf M r b c n f rb rc rn delta ub uc fr HO HR HC HFR).
    + apply (proj1 (proj2 HP) b c n (zeroM M) rb rc rn delta ub uc (zeroM M) HS HC).
      apply (proj2 (numerical_renaming_invalid M (zeroM M) rb rc rn delta (zeroM M) (or_introl eq_refl))). reflexivity.
  - destruct H as (b & c & n & a & d & f & HR & HS & HF).
    apply (source_proof_renaming_ordinary_intro M r b c n a HO HR).
    intros rb rc rn delta ub uc ar HC HA.
    destruct (numerical_renaming_total M d rb rc rn delta) as [dr HD].
    destruct (numerical_renaming_total M f rb rc rn delta) as [fr HFR].
    apply (full_source_CE1 M ub uc n ar dr fr).
    + exact (source_proof_renaming_target_wf M r b c n a rb rc rn delta ub uc ar HO HR HC HA).
    + exact (proj1 (proj2 HP) b c n f rb rc rn delta ub uc fr HS HC HFR).
    + exact (source_binary_renaming_graph M SFAnd a d f rb rc rn delta ar dr fr (or_introl eq_refl) HF HA HD HFR).
  - destruct H as (b & c & n & a & d & f & HR & HS & HF).
    apply (source_proof_renaming_ordinary_intro M r b c n d HO HR).
    intros rb rc rn delta ub uc dr HC HD.
    destruct (numerical_renaming_total M a rb rc rn delta) as [ar HA].
    destruct (numerical_renaming_total M f rb rc rn delta) as [fr HFR].
    apply (full_source_CE2 M ub uc n ar dr fr).
    + exact (source_proof_renaming_target_wf M r b c n d rb rc rn delta ub uc dr HO HR HC HD).
    + exact (proj1 (proj2 HP) b c n f rb rc rn delta ub uc fr HS HC HFR).
    + exact (source_binary_renaming_graph M SFAnd a d f rb rc rn delta ar dr fr (or_introl eq_refl) HF HA HD HFR).
  - destruct H as (b & c & n & a & d & f & HR & HS & HF).
    apply (source_proof_renaming_ordinary_intro M r b c n f HO HR).
    intros rb rc rn delta ub uc fr HC HFR.
    destruct (numerical_renaming_total M a rb rc rn delta) as [ar HA].
    destruct (numerical_renaming_total M d rb rc rn delta) as [dr HD].
    apply (full_source_DI1 M ub uc n ar dr fr).
    + exact (source_proof_renaming_target_wf M r b c n f rb rc rn delta ub uc fr HO HR HC HFR).
    + exact (proj1 (proj2 HP) b c n a rb rc rn delta ub uc ar HS HC HA).
    + exact (source_binary_renaming_graph M SFOr a d f rb rc rn delta ar dr fr (or_intror (or_introl eq_refl)) HF HA HD HFR).
  - destruct H as (b & c & n & a & d & f & HR & HS & HF).
    apply (source_proof_renaming_ordinary_intro M r b c n f HO HR).
    intros rb rc rn delta ub uc fr HC HFR.
    destruct (numerical_renaming_total M a rb rc rn delta) as [ar HA].
    destruct (numerical_renaming_total M d rb rc rn delta) as [dr HD].
    apply (full_source_DI2 M ub uc n ar dr fr).
    + exact (source_proof_renaming_target_wf M r b c n f rb rc rn delta ub uc fr HO HR HC HFR).
    + exact (proj1 (proj2 HP) b c n d rb rc rn delta ub uc dr HS HC HD).
    + exact (source_binary_renaming_graph M SFOr a d f rb rc rn delta ar dr fr (or_intror (or_introl eq_refl)) HF HA HD HFR).
Qed.

Print Assumptions source_proof_renaming_base.
Print Assumptions source_proof_renaming_prop_unary.
