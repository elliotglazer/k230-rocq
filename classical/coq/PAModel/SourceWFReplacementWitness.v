(** The actual guarded Replacement range witness is WF, and its profile
    gives the exact WF-relative output profile, with the same input witness. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SetSchemaConstructors SourceBounded SchemaConstructorBounds SourceNumeralLift
  NumericalContexts NumericalContextRenaming NumericalSourceFull SourceRelativizationBounds
  SourceUniversalPropositional SourcePropositionalTemplates SourcePropositionalRebase
  SourceWFFormula NumericalWFFoundation WFClosureFiniteBridge WFClosureInstantiation
  WFSubsetInstantiation SourceWFSeparationWitness SourceWFSeparationConstructor
  SourceWFSeparationExistential SourceWFReplacementBody SourceWFReplacementExistential
  SourceWFReplacementMembers SourceWFReplacementProfiles SourceWFReplacementProfileGraphs
  SourceWFReplacementPoint SourceQuantifierRules.
From Undecidability.FOL Require Import Sets.minZF.
Unset Implicit Arguments.
Open Scope minZFsyn.

Definition source_wf_members_point_code M :=
  code_numeral M (sf_encode ($0 ∈' $1 → wf_class $0)).
Lemma source_wf_members_graphs M :
  sf_relation M SFImpl (source_sep_left_code M) (source_wf_domain_code M) (source_wf_members_point_code M) /\
  sf_relation M SFAll (source_wf_members_point_code M) (zeroM M) (source_wf_members_code M).
Proof.
  split.
  - exact (source_formula_implication_numeral M source_sep_left (wf_class $0)).
  - exact (source_formula_universal_numeral M ($0 ∈' $1 → wf_class $0)).
Qed.
Lemma source_wf_domain1_shift M :
  source_formula_shift M (source_wf_domain_code M) (source_wf_domain1_code M).
Proof. exact (source_wf_domain_shift M). Qed.
Local Opaque source_wf_domain_code source_wf_domain1_code source_rep_input_code source_sep_left_code
  source_wf_members_code source_wf_members_point_code source_wf_closure_code.

Theorem source_full_WF_replacement_witness M b c l n theta rawprofile targetprofile witness :
  context_bounded M b c l (succM M (succM M n)) ->
  source_bounded M theta (succM M (succM M (succM M (succM M n)))) ->
  source_wf_rep_raw_profile_graph M theta rawprofile ->
  source_wf_rep_target_profile_graph M theta targetprofile ->
  sf_relation M SFAnd (source_wf_domain_code M) targetprofile witness ->
  source_full_prv M b c l (source_wf_closure_code M) ->
  source_full_prv M b c l rawprofile ->source_full_prv M b c l witness.
Proof.
  intros HC HTheta HRaw HTarget HW PClosure PRaw.
  pose proof (source_wf_rep_target_profile_bound M theta targetprofile n HTheta HTarget) as HTargetBound.
  unfold source_wf_rep_raw_profile_graph,E_wf_rep_raw_profile,E_sf_all in HRaw.
  destruct (schema_expression_quantifier_split M _ SFAll _ rawprofile HRaw)
    as [rawpoint [HRawPoint HRawAll]].
  destruct (code_relation_total M (E_sf_ex (E_sf SFAnd (E_sf_mem 0 3)
    (E_sf SFAnd (E_sf SFAnd (CEvar 0) (CEvar 1)) (CEvar 2)))) (wf_rep_profile_env M theta))
    as [rawex HRawEx].
  destruct (source_rep_atom_graphs M (wf_rep_profile_env M theta)) as [HLeft HInput].
  destruct (schema_iff_split M _ _ _ _ _ rawpoint HLeft HRawEx HRawPoint)
    as [rawforward [rawreverse [HRF [HRR HRP]]]].
  destruct (schema_expression_quantifier_split M _ SFEx _ rawex HRawEx)
    as [rawbody [HRawBody HRawExists]].
  assert (HRBody:code_relation M (wf_rep_env (source_wf_domain_code M) (source_wf_domain1_code M)
    (source_rep_input_code M) theta) (source_prop_expression wf_rep_raw_body) rawbody).
  { apply (proj1 (source_rep_body_rebase M theta wf_rep_raw_body rawbody)). exact HRawBody. }
  destruct (schema_expression_split M _ SFAnd _ _ rawbody HRawBody)
    as [input [matrix [HI [HM HBody]]]].
  pose proof (code_relation_functional M _ _ input (source_rep_input_code M) HI HInput) as EI. subst input.
  destruct (schema_expression_split M _ SFAnd _ _ matrix HM) as [guards [th [HG [HTh HMatrix]]]].
  change (th=theta) in HTh. subst th.
  destruct (schema_expression_split M _ SFAnd _ _ guards HG) as [d [d1 [HD [HD1 HGuards]]]].
  change (d=source_wf_domain_code M) in HD. change (d1=source_wf_domain1_code M) in HD1. subst d d1.
  unfold source_wf_rep_target_profile_graph,E_wf_rep_target_profile,E_sf_all in HTarget.
  destruct (schema_expression_quantifier_split M _ SFAll _ targetprofile HTarget)
    as [guardpoint [HGuardPoint HTargetAll]].
  destruct (schema_expression_split M _ SFImpl _ _ guardpoint HGuardPoint)
    as [d [targetpoint [HD [HTargetPoint HGuard]]]].
  change (d=source_wf_domain_code M) in HD. subst d.
  destruct (code_relation_total M (E_sf_ex (E_sf SFAnd (CEvar 0)
    (E_sf SFAnd (E_sf_mem 0 3) (CEvar 2)))) (wf_rep_profile_env M theta)) as [targetex HTargetEx].
  destruct (schema_iff_split M _ _ _ _ _ targetpoint HLeft HTargetEx HTargetPoint)
    as [forward [reverse [HF [HR HP]]]].
  destruct (schema_expression_quantifier_split M _ SFEx _ targetex HTargetEx)
    as [targetbody [HTargetBody HTargetExists]].
  assert (HTBody:code_relation M (wf_rep_env (source_wf_domain_code M) (source_wf_domain1_code M)
    (source_rep_input_code M) theta) (source_prop_expression wf_rep_target_body) targetbody).
  { apply (proj1 (source_rep_body_rebase M theta wf_rep_target_body targetbody)). exact HTargetBody. }
  pose proof (source_wf_domain1_shift M) as HDShift.
  pose proof (numerical_wf_domain_bounded M) as HDBound.
  assert (HSlotBounds:forall i,source_bounded M
    (wf_rep_env (source_wf_domain_code M) (source_wf_domain1_code M) (source_rep_input_code M) theta i)
    (succM M (succM M (succM M (succM M n))))).
  { intros [|[|[|i]]];cbn [wf_rep_env].
    - exact (sr_domain_bound_succ M _ (succM M (succM M (succM M n))) HDBound).
    - exact (source_rep_domain1_bound M (succM M (succM M n))).
    - exact (source_rep_input_bound M n).
    - exact HTheta. }
  assert (PTarget:source_full_prv M b c l targetprofile).
  { destruct (context_shift_total M b c l) as [s [t HS]].
    apply (full_source_AllI M b c l guardpoint targetprofile s t
      (ex_intro _ (succM M (succM M n)) (conj HTargetBound HC)));[|exact HS|exact HTargetAll].
    destruct (source_sep_atom_bounds M n) as [HL _].
    apply (source_full_wf_rep_guarded_point M s t l (succM M (succM M (succM M n)))
      (source_wf_domain_code M) (source_wf_domain1_code M) (source_rep_input_code M) theta
      rawbody targetbody rawex targetex (source_sep_left_code M) rawforward rawreverse rawpoint
      forward reverse targetpoint guardpoint HSlotBounds
      (context_shift_preserves_bound M b c l s t (succM M (succM M n)) HS HC)
      (sr_domain_bound_succ M _ (succM M (succM M n)) HDBound) HL HDShift
      HRBody HTBody HRawExists HTargetExists HRF HRR HRP HF HR HP HGuard).
    exact (source_full_all_shift M b c l rawpoint rawprofile s t HRawAll PRaw HS). }
  destruct (source_wf_members_graphs M) as [HMembersPoint HMembersAll].
  pose proof (source_full_replacement_members M b c l (source_wf_domain_code M) (source_wf_domain1_code M)
    theta (source_rep_input_code M) guards matrix rawbody rawex (source_sep_left_code M)
    rawforward rawreverse rawpoint rawprofile (source_wf_members_point_code M) (source_wf_members_code M)
    HDBound HDShift HGuards HMatrix HBody HRawExists HRF HRP HRawAll HMembersPoint HMembersAll PRaw) as PMembers.
  pose proof (@numerical_wf_closure_at_witness M b c l PClosure PMembers) as PWF.
  apply (full_source_CI M b c l (source_wf_domain_code M) targetprofile witness);[|exact PWF|exact PTarget|exact HW].
  exists (succM M (succM M n)). split;[|exact HC].
  apply (proj2 (source_bounded_accept_binary M SFAnd (source_wf_domain_code M) targetprofile witness _
    (or_introl eq_refl) HW)). split;[exact (sr_domain_bound_succ M _ (succM M n) HDBound)|exact HTargetBound].
Qed.

Print Assumptions source_wf_members_graphs.
Print Assumptions source_full_WF_replacement_witness.
