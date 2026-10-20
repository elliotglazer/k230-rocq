(** Actual guarded raw Replacement range to the relative range profile,
    preserving the original output-set witness and every free parameter. *)
From PAModel Require Import Model FiniteCoding CodeExpressions ProofTemplates SetFormulaCodes SetSchemaConstructors SchemaConstructorBounds SourceBounded
 NumericalContexts NumericalContextRenaming NumericalEnvironments NumericalRenaming NumericalSourceFull SourceTraceBounds SourceQuantifierRules
 SourceRelativizationBounds SourceImplicationAllShift SourceContextTransport SourcePropositionalRebase SourceWFSeparationConstructor SourceWFReplacementProfiles
 SourceLReplacementPsiR SourceLReplacementCutShells SourceLReplacementCutSelection SourceGuardedReplacementProfile SourceExistentialMap.
Unset Implicit Arguments.
Theorem source_full_guarded_L_range M domain domain1 matrix theta raw target b c l n:
 source_bounded M domain(code_numeral M 1) ->source_formula_shift M domain domain1 ->
 source_bounded M matrix(succM M(succM M(succM M(succM M n)))) ->
 context_bounded M b c l(succM M n) ->
 code_relation M(schema_env3 domain domain1 matrix)
  (E_sf_ex(E_wf_rep_raw_profile(CEvar 0)(CEvar 1)(CEvar 2)))raw ->
 code_relation M(schema_env3 domain matrix(zeroM M))(E_L_replacement_theta(CEvar 0)(CEvar 1))theta ->
 code_relation M(schema_env3 domain theta(zeroM M))(E_sf_ex(E_L_range_profile(CEvar 0)(CEvar 1)1))target ->
 source_full_prv M b c l raw ->source_full_prv M b c l target.
Proof.
 intros HD HDShift HM HC HR HTheta HT PR.
 assert(BD1:source_bounded M domain1(succM M(succM M(succM M(succM M n))))).
 { exact(source_shift_bound M domain domain1(succM M(succM M(succM M n)))
   (sr_domain_bound_succ M domain(succM M(succM M n))HD)HDShift). }
 assert(BTheta:source_bounded M theta(succM M(succM M(succM M n)))).
 { assert(B:schema_expression_bound M(schema_env3 domain matrix(zeroM M))
   (E_L_replacement_theta(CEvar 0)(CEvar 1))(succM M(succM M(succM M n)))).
   { unfold E_L_replacement_theta,E_sf_ex,E_sf_mem. lrep_shell_bound. } exact(B theta HTheta). }
 assert(BTarget:source_bounded M target(succM M n)).
 { assert(B:schema_expression_bound M(schema_env3 domain theta(zeroM M))
   (E_sf_ex(E_L_range_profile(CEvar 0)(CEvar 1)1))(succM M n)).
   { unfold E_L_range_profile,E_sf_iff,E_sf_all,E_sf_ex,E_sf_mem. lrep_shell_bound. } exact(B target HT). }
 unfold E_sf_ex in HR,HT.
 destruct(schema_expression_quantifier_split M _ SFEx _ raw HR)as(rp&HRP&HRawEx).
 destruct(schema_expression_quantifier_split M _ SFEx _ target HT)as(tp&HTP&HTargetEx).
 assert(BRP:source_bounded M rp(succM M(succM M n))).
 { assert(B:schema_expression_bound M(schema_env3 domain domain1 matrix)
   (E_wf_rep_raw_profile(CEvar 0)(CEvar 1)(CEvar 2))(succM M(succM M n))).
   { unfold E_wf_rep_raw_profile,E_sf_iff,E_sf_all,E_sf_ex,E_sf_mem. lrep_shell_bound. }
   exact(B rp HRP). }
 assert(HTP':code_relation M(schema_env3 domain domain1 matrix)(E_wf_rep_target_profile(CEvar 0)(CEvar 2))tp).
 { apply(proj2(code_subst_graph M(schema_env3 domain domain1 matrix)
   (fun i=>match i with 0=>CEvar 0|1=>E_L_replacement_theta(CEvar 0)(CEvar 2)|_=>CEconst 0 end)
   (schema_env3 domain theta(zeroM M))ltac:(intros[|[|i]];try reflexivity;exact HTheta)
   (E_L_range_profile(CEvar 0)(CEvar 1)1)tp)). exact HTP. }
 destruct(context_shift_total M b c l)as(us&vs&HShift).
 destruct(environment_cons_total M us vs l rp)as(ub&uc&un&HCons).
 assert(HBC:context_bounded M ub uc un(succM M(succM M n))).
 { apply(proj2(context_bounded_cons M us vs l rp ub uc un _ HCons)).
   split;[exact BRP|exact(context_shift_preserves_bound M b c l us vs(succM M n)HShift HC)]. }
 assert(PRP:source_full_prv M ub uc un rp).
 { apply full_source_Ctx;[exists(succM M(succM M n));auto|].
   apply(proj2(context_member_cons M us vs l rp ub uc un rp HCons));now left. }
 pose proof(source_full_guarded_replacement_profile M domain domain1 matrix ub uc un n rp tp HD HDShift HBC HM HRP HTP' PRP)as PTP.
 destruct(numerical_renaming_total M target(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1))as(shifted&HShifted).
 exact(source_full_exists_map M b c l rp tp raw target us vs ub uc un shifted
  (ex_intro _ (succM M n)(conj BTarget HC))HRawEx HTargetEx HShift HCons HShifted PR PTP).
Qed.
Print Assumptions source_full_guarded_L_range.



