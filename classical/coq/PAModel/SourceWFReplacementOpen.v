(** Replacement's outer forall/exists shell preserves the raw output set.
    The range profile proof needs no assumption on the input set. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes
  SourceBounded SetSchemaConstructors SchemaConstructorBounds NumericalContexts NumericalEnvironments
  NumericalContextRenaming NumericalRenaming SourceQuantifierRules NumericalSourceFull
  SourceProofRenaming SourceProofWeakening SourceContextTransport SourceUniversalPropositional
  SourceExistentialMap SourceUniversalGuard SourceNumeralLift SourceRelativizationBounds
  SourceImplicationAllShift SourceWFFormula NumericalWFFoundation WFClosureFiniteBridge
  SourceWFSeparationExistential SourceWFReplacementProfiles SourceWFReplacementWitness.
From Undecidability.FOL Require Import Syntax.Core Sets.minZF.
From FOL Require Import FullSyntax.
Unset Implicit Arguments.
Open Scope minZFsyn.

Lemma source_wf_closure_shift M :
  source_formula_shift M (source_wf_closure_code M) (source_wf_closure_code M).
Proof.
  pose proof (source_formula_numeral_shift M source_wf_closure) as H.
  assert (E:subst_form ↑ source_wf_closure=source_wf_closure).
  { unfold source_wf_closure. wf_simp. reflexivity. }
  now rewrite E in H.
Qed.

Lemma source_wf_domain1_shift M :
  source_formula_shift M (source_wf_domain_code M) (source_wf_domain1_code M).
Proof. exact (source_wf_domain_shift M). Qed.

Local Opaque source_wf_domain_code source_wf_domain1_code source_wf_closure_code.

Lemma source_wf_rep_raw_profile_bound M theta profile n :
  source_bounded M theta (succM M (succM M (succM M (succM M n)))) ->
  source_wf_rep_raw_profile_graph M theta profile ->
  source_bounded M profile (succM M (succM M n)).
Proof.
  intros HT HP.
  assert (HD1:source_bounded M (source_wf_domain1_code M)
    (succM M (succM M (succM M (succM M n))))).
  { exact (source_shift_bound M (source_wf_domain_code M) (source_wf_domain1_code M)
      (succM M (succM M (succM M n)))
      (sr_domain_bound_succ M _ (succM M (succM M n)) (numerical_wf_domain_bounded M))
      (source_wf_domain1_shift M)). }
  assert (HB:schema_expression_bound M (wf_rep_profile_env M theta)
    (E_wf_rep_raw_profile (CEvar 0) (CEvar 1) (CEvar 2)) (succM M (succM M n))).
  { unfold E_wf_rep_raw_profile,E_sf_all,E_sf_ex,E_sf_mem.
    apply schema_expression_unary;[now left|].
    apply schema_expression_iff.
    - apply schema_expression_atom;[now left|schema_small_index|schema_small_index].
    - apply schema_expression_unary;[now right|].
      apply schema_expression_binary;[now left| |].
      + apply schema_expression_atom;[now left|schema_small_index|schema_small_index].
      + apply schema_expression_binary;[now left| |].
        * apply schema_expression_binary;[now left| |].
          -- apply schema_expression_variable. cbn [wf_rep_profile_env schema_env3].
             apply sr_domain_bound_succ. exact (numerical_wf_domain_bounded M).
          -- apply schema_expression_variable. exact HD1.
        * apply schema_expression_variable. exact HT. }
  exact (HB profile HP).
Qed.

Theorem source_full_WF_replacement_rhs_graphs M b c l n theta rawprofile rawex raw
    targetprofile witness targetex outerguard target :
  context_bounded M b c l n ->
  source_bounded M theta (succM M (succM M (succM M (succM M n)))) ->
  source_wf_rep_raw_profile_graph M theta rawprofile ->
  source_wf_rep_target_profile_graph M theta targetprofile ->
  sf_relation M SFEx rawprofile (zeroM M) rawex ->sf_relation M SFAll rawex (zeroM M) raw ->
  sf_relation M SFAnd (source_wf_domain_code M) targetprofile witness ->
  sf_relation M SFEx witness (zeroM M) targetex ->
  sf_relation M SFImpl (source_wf_domain_code M) targetex outerguard ->
  sf_relation M SFAll outerguard (zeroM M) target ->source_bounded M target n ->
  source_full_prv M b c l (source_wf_closure_code M) ->source_full_prv M b c l raw ->
  source_full_prv M b c l target.
Proof.
  intros HC HT HRawProfile HTargetProfile HRawEx HRawAll HW HEx HOuter HTarget HBound PC PR.
  pose proof (source_wf_rep_raw_profile_bound M theta rawprofile n HT HRawProfile) as HRBound.
  pose proof (proj1 (source_bounded_accept_unary M SFAll outerguard target n
    (or_introl eq_refl) HTarget) HBound) as HOuterBound.
  pose proof (proj2 (proj1 (source_bounded_accept_binary M SFImpl
    (source_wf_domain_code M) targetex outerguard (succM M n)
    (or_intror (or_intror eq_refl)) HOuter) HOuterBound)) as HExBound.
  destruct (context_shift_total M b c l) as [s [t HS]].
  pose proof (context_shift_preserves_bound M b c l s t n HS HC) as HSC.
  pose proof (source_full_all_shift M b c l rawex raw s t HRawAll PR HS) as PRawEx.
  pose proof (source_full_prv_renaming M b c l (source_wf_closure_code M)
    (zeroM M) (zeroM M) (zeroM M) (succM M (zeroM M)) s t
    (source_wf_closure_code M) PC HS (source_wf_closure_shift M)) as PCS.
  destruct (context_shift_total M s t l) as [s2 [t2 HS2]].
  pose proof (context_shift_preserves_bound M s t l s2 t2 (succM M n) HS2 HSC) as HSC2.
  destruct (environment_cons_total M s2 t2 l rawprofile) as [u [v [j HCons]]].
  assert (HBranch:context_bounded M u v j (succM M (succM M n))).
  { exact (proj2 (context_bounded_cons M s2 t2 l rawprofile u v j _ HCons) (conj HRBound HSC2)). }
  assert (HI:context_included M s2 t2 l u v j).
  { intros a HA. apply (proj2 (context_member_cons M s2 t2 l rawprofile u v j a HCons)). now right. }
  pose proof (source_full_prv_renaming M s t l (source_wf_closure_code M)
    (zeroM M) (zeroM M) (zeroM M) (succM M (zeroM M)) s2 t2
    (source_wf_closure_code M) PCS HS2 (source_wf_closure_shift M)) as PCS2.
  assert (PCBranch:source_full_prv M u v j (source_wf_closure_code M)).
  { exact (source_full_prv_weaken_bounded M s2 t2 l u v j _ _ PCS2 HI HBranch). }
  assert (PProfile:source_full_prv M u v j rawprofile).
  { apply full_source_Ctx.
    - exists (succM M (succM M n)). auto.
    - apply (proj2 (context_member_cons M s2 t2 l rawprofile u v j rawprofile HCons)). now left. }
  pose proof (source_full_WF_replacement_witness M u v j n theta rawprofile targetprofile witness
    HBranch HT HRawProfile HTargetProfile HW PCBranch PProfile) as PWitness.
  destruct (numerical_renaming_total M targetex (zeroM M) (zeroM M) (zeroM M)
    (succM M (zeroM M))) as [shifted HShift].
  pose proof (source_full_exists_map M s t l rawprofile witness rawex targetex s2 t2 u v j shifted
    (ex_intro _ (succM M n) (conj HExBound HSC)) HRawEx HEx HS2 HCons HShift PRawEx PWitness) as PEx.
  destruct (sf_relation_total M SFAll targetex (zeroM M)) as [bare HBare].
  assert (HBareBound:source_bounded M bare n).
  { exact (proj2 (source_bounded_accept_unary M SFAll targetex bare n (or_introl eq_refl) HBare) HExBound). }
  pose proof (full_source_AllI M b c l targetex bare s t (ex_intro _ n (conj HBareBound HC))
    PEx HS HBare) as PBare.
  exact (source_full_universal_guard M (source_wf_domain_code M) b c l targetex bare outerguard target
    (numerical_wf_domain_bounded M) HBare HOuter HTarget PBare).
Qed.

Print Assumptions source_wf_closure_shift.
Print Assumptions source_wf_rep_raw_profile_bound.
Print Assumptions source_full_WF_replacement_rhs_graphs.
