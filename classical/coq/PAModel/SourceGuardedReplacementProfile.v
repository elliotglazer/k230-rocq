(** Pure guarded-profile conversion for an arbitrary one-variable domain.
    The ambient output set is retained, without claiming it belongs to the
    domain. This uses only ordinary source rules and the same input witness. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SetSchemaConstructors
 SourceBounded SchemaConstructorBounds SourceNumeralLift NumericalContexts NumericalContextRenaming NumericalSourceFull
 SourceRelativizationBounds SourceUniversalPropositional SourcePropositionalTemplates SourcePropositionalRebase
 SourceWFSeparationWitness SourceWFSeparationConstructor SourceWFSeparationExistential SourceWFReplacementBody SourceWFReplacementExistential
 SourceWFReplacementProfiles SourceWFReplacementProfileGraphs SourceWFReplacementPoint SourceQuantifierRules SourceImplicationAllShift.
Unset Implicit Arguments.
Local Opaque source_sep_left_code source_rep_input_code.
Theorem source_full_guarded_replacement_profile M domain domain1 theta b c l n rawprofile targetprofile:
 source_bounded M domain(code_numeral M 1) ->source_formula_shift M domain domain1 ->
 context_bounded M b c l(succM M(succM M n)) ->
 source_bounded M theta(succM M(succM M(succM M(succM M n)))) ->
 code_relation M(schema_env3 domain domain1 theta)(E_wf_rep_raw_profile(CEvar 0)(CEvar 1)(CEvar 2))rawprofile ->
 code_relation M(schema_env3 domain domain1 theta)(E_wf_rep_target_profile(CEvar 0)(CEvar 2))targetprofile ->
 source_full_prv M b c l rawprofile ->source_full_prv M b c l targetprofile.
Proof.
 intros HD HDShift HC HTheta HRaw HTarget PRaw.
 set(rho:=schema_env3 domain domain1 theta).
 assert(BDomain1:source_bounded M domain1(succM M(succM M(succM M(succM M n))))).
 { exact(source_shift_bound M domain domain1(succM M(succM M(succM M n)))
   (sr_domain_bound_succ M domain(succM M(succM M n))HD)HDShift). }
 assert(HTargetBound:source_bounded M targetprofile(succM M(succM M n))).
 { assert(B:schema_expression_bound M rho(E_wf_rep_target_profile(CEvar 0)(CEvar 2))(succM M(succM M n))).
   { unfold E_wf_rep_target_profile,E_sf_all,E_sf_ex,E_sf_mem.
     repeat schema_constructor_bound;try schema_small_index;cbn[rho schema_env3];try exact HTheta;
     apply sr_domain_bound_succ;exact HD. }
   exact(B targetprofile HTarget). }
 unfold E_wf_rep_raw_profile,E_sf_all in HRaw.
 destruct(schema_expression_quantifier_split M _ SFAll _ rawprofile HRaw)as(rawpoint&HRawPoint&HRawAll).
 destruct(code_relation_total M(E_sf_ex(E_sf SFAnd(E_sf_mem 0 3)(E_sf SFAnd(E_sf SFAnd(CEvar 0)(CEvar 1))(CEvar 2))))rho)as(rawex&HRawEx).
 destruct(source_rep_atom_graphs M rho)as(HLeft&HInput).
 destruct(schema_iff_split M _ _ _ _ _ rawpoint HLeft HRawEx HRawPoint)as(rawforward&rawreverse&HRF&HRR&HRP).
 destruct(schema_expression_quantifier_split M _ SFEx _ rawex HRawEx)as(rawbody&HRawBody&HRawExists).
 assert(HRBody:code_relation M(wf_rep_env domain domain1(source_rep_input_code M)theta)(source_prop_expression wf_rep_raw_body)rawbody).
 { apply(proj1(source_prop_expression_with_graph M rho
    (fun i=>match i with 0=>CEvar 0|1=>CEvar 1|2=>E_sf_mem 0 3|_=>CEvar 2 end)
    (wf_rep_env domain domain1(source_rep_input_code M)theta)wf_rep_raw_body
    ltac:(intros[|[|[|i]]];cbn[rho schema_env3 wf_rep_env];try reflexivity;exact HInput)rawbody)). exact HRawBody. }
 unfold E_wf_rep_target_profile,E_sf_all in HTarget.
 destruct(schema_expression_quantifier_split M _ SFAll _ targetprofile HTarget)as(guardpoint&HGuardPoint&HTargetAll).
 destruct(schema_expression_split M _ SFImpl _ _ guardpoint HGuardPoint)as(d&targetpoint&HD'&HTargetPoint&HGuard).
 change(d=domain)in HD'. subst d.
 destruct(code_relation_total M(E_sf_ex(E_sf SFAnd(CEvar 0)(E_sf SFAnd(E_sf_mem 0 3)(CEvar 2))))rho)as(targetex&HTargetEx).
 destruct(schema_iff_split M _ _ _ _ _ targetpoint HLeft HTargetEx HTargetPoint)as(forward&reverse&HF&HR&HP).
 destruct(schema_expression_quantifier_split M _ SFEx _ targetex HTargetEx)as(targetbody&HTargetBody&HTargetExists).
 assert(HTBody:code_relation M(wf_rep_env domain domain1(source_rep_input_code M)theta)(source_prop_expression wf_rep_target_body)targetbody).
 { apply(proj1(source_prop_expression_with_graph M rho
    (fun i=>match i with 0=>CEvar 0|1=>CEvar 1|2=>E_sf_mem 0 3|_=>CEvar 2 end)
    (wf_rep_env domain domain1(source_rep_input_code M)theta)wf_rep_target_body
    ltac:(intros[|[|[|i]]];cbn[rho schema_env3 wf_rep_env];try reflexivity;exact HInput)targetbody)). exact HTargetBody. }
 assert(HSlotBounds:forall i,source_bounded M(wf_rep_env domain domain1(source_rep_input_code M)theta i)
  (succM M(succM M(succM M(succM M n))))).
 { intros[|[|[|i]]];cbn[wf_rep_env].
   - exact(sr_domain_bound_succ M domain(succM M(succM M(succM M n)))HD).
   - exact BDomain1.
   - exact(source_rep_input_bound M n).
   - exact HTheta. }
 destruct(context_shift_total M b c l)as(sb&sc&HShift).
 apply(full_source_AllI M b c l guardpoint targetprofile sb sc(ex_intro _ (succM M(succM M n))(conj HTargetBound HC)));[|exact HShift|exact HTargetAll].
 destruct(source_sep_atom_bounds M n)as[HL _].
 apply(source_full_wf_rep_guarded_point M sb sc l(succM M(succM M(succM M n)))domain domain1(source_rep_input_code M)theta
  rawbody targetbody rawex targetex(source_sep_left_code M)rawforward rawreverse rawpoint forward reverse targetpoint guardpoint
  HSlotBounds(context_shift_preserves_bound M b c l sb sc(succM M(succM M n))HShift HC)
  (sr_domain_bound_succ M domain(succM M(succM M n))HD)HL HDShift HRBody HTBody HRawExists HTargetExists HRF HRR HRP HF HR HP HGuard).
 exact(source_full_all_shift M b c l rawpoint rawprofile sb sc HRawAll PRaw HShift).
Qed.
Print Assumptions source_full_guarded_replacement_profile.
