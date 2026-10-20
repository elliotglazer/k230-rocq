(** All matrix allocations for the ordinary L range cut are actual
    arithmetic cutoff transformations, including the unused witness slots. *)
From PAModel Require Import Model FiniteCoding CodeExpressions ProofTemplates SetFormulaCodes SetSchemaConstructors SchemaConstructorBounds SourceBounded
 SourceFiniteCutoffShift SourceCutoffShiftCommutation SourceCutoffQuantifiers SourceLSeparationMatrixShift SchemaRenamingDescriptors
 SourceLReplacementCutShells SourceWFReplacementProfiles SourceWFReplacementConstructor SourceFunctionalityShells
 SourceRelativizationBounds SourceSchemaRelativization SourceRelativeSchemaConstructors QuotationSchemaSkeleton.
Unset Implicit Arguments.
Theorem source_L_replacement_cutoff_slots M rpsi theta first second count:
 source_bounded M rpsi(succM M(succM M count)) ->source_cutoff_shift M 1 rpsi theta ->
 source_cutoff_shift M 2 theta first ->source_cutoff_shift M 3 first second ->
 source_bounded M theta(succM M(succM M(succM M count))) /\
 source_bounded M first(succM M(succM M(succM M(succM M count)))) /\
 source_bounded M second(succM M(succM M(succM M(succM M(succM M count))))) /\
 source_cutoff_shift M 1 theta first /\source_cutoff_shift M 1 first second /\
 source_cutoff_shift M 2 first second /\schema_renaming M SepBody rpsi first.
Proof.
 intros HB HT HF HS.
 pose proof(source_cutoff_shift_bounded M 1 rpsi theta(succM M count)HB HT)as BT.
 pose proof(source_cutoff_shift_bounded M 2 theta first(succM M count)BT HF)as BF.
 pose proof(source_cutoff_shift_bounded M 3 first second(succM M count)BF HS)as BS.
 pose proof(source_cutoff_one_two_commute M rpsi theta theta first(succM M(succM M count))HB HT HT HF)as H1.
 pose proof(source_cutoff_two_three_commute M theta first first second(succM M(succM M(succM M count)))BT HF HF HS)as H2.
 pose proof(source_cutoff_one_two_commute M theta first first second(succM M(succM M(succM M count)))BT H1 H1 H2)as H3.
 pose proof(source_cutoff_twice_is_SepBody M rpsi theta first(succM M(succM M count))HB HT H1)as HSep.
 repeat split;assumption.
Qed.
Theorem source_L_guarded_range_rebase M domain domain1 rc ma mb mc guards raw:
 sf_relation M SFAnd domain domain1 guards ->sf_relation M SFAnd guards rc mc ->
 code_relation M(schema_env3 ma mb mc)(E_sf_ex(E_replacement_raw_profile(CEvar 2)))raw ->
 code_relation M(schema_env3 domain domain1 rc)(E_sf_ex(E_wf_rep_raw_profile(CEvar 0)(CEvar 1)(CEvar 2)))raw.
Proof.
 intros HG HM HR.
 apply(proj2(code_subst_graph M(schema_env3 domain domain1 rc)
  (fun i=>match i with 0=>CEconst 0|1=>CEconst 0|_=>E_sf SFAnd(E_sf SFAnd(CEvar 0)(CEvar 1))(CEvar 2)end)
  (schema_env3(zeroM M)(zeroM M)mc)ltac:(intros[|[|i]];try reflexivity;functionality_graph)
   (E_sf_ex(E_replacement_raw_profile(CEvar 2)))raw)).
 apply(proj1(code_subst_graph M(schema_env3 ma mb mc)(fun _=>CEvar 2)(fun _=>mc)
   ltac:(intro i;reflexivity)(E_sf_ex(E_replacement_raw_profile(CEvar 0)))raw))in HR.
 exact(proj2(code_subst_graph M(schema_env3(zeroM M)(zeroM M)mc)(fun _=>CEvar 2)(fun _=>mc)
   ltac:(intro i;reflexivity)(E_sf_ex(E_replacement_raw_profile(CEvar 0)))raw)HR).
Qed.
Theorem source_relative_replacement_constructor_bound M domain ra rb rc target count:
 source_bounded M domain(code_numeral M 1) ->
 source_bounded M ra(succM M(succM M(succM M count))) ->source_bounded M rb(succM M(succM M(succM M count))) ->
 source_bounded M rc(succM M(succM M(succM M(succM M count)))) ->
 sf_relative_replacement_constructor M domain ra rb rc target ->source_bounded M target count.
Proof.
 intros HD HA HB HC HT. unfold sf_relative_replacement_constructor in HT. rewrite relative_replacement_skeleton_exact in HT.
 assert(B:schema_expression_bound M(skeleton_relative_environment domain(schema_env3 ra rb rc))
   (E_sf_relative_replacement(CEvar 0)(CEvar 1)(CEvar 2)(CEvar 3))count).
 { unfold E_sf_relative_replacement,E_sf_relative_functionality,E_sf_relative_all,E_sf_relative_ex,E_sf_all,E_sf_ex,E_sf_mem,E_sf_eq.
   repeat schema_constructor_bound;try schema_small_index;cbn[skeleton_relative_environment schema_env3];try assumption;
   apply sr_domain_bound_succ;exact HD. }
 exact(B target HT).
Qed.
Print Assumptions source_L_replacement_cutoff_slots.
Print Assumptions source_L_guarded_range_rebase.
Print Assumptions source_relative_replacement_constructor_bound.
