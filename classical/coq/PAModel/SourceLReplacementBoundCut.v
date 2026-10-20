(** Actual existential elimination of the covering L-level. Relative
    Separation is used at that very level and cuts the same raw range. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SetSchemaConstructors SchemaConstructorBounds SourceBounded
 NumericalContexts NumericalContextRenaming NumericalEnvironments NumericalRenaming NumericalSourceFull SourceTraceBounds SourceProofWeakening SourceProofRenaming
 SourceContextTransport SourceConjunctionRules SourceDerivedRules SourceQuantifierRules SourceExistentialMap
 SourceRelativizationBounds SourceUniversalPropositional SourcePropositionalRebase SourceWFSeparationConstructor
 SourceLReplacementCutShells SourceLReplacementCutSelection SourceFiniteCutoffShift SourceCutoffPropositional.
Unset Implicit Arguments.
Definition E_L_separation_law d matrix:=E_sf_all(E_sf SFImpl d(E_L_selection_witness d matrix)).
Theorem source_full_L_range_cut_by_bound M domain theta first second range bound separation target b c l n:
 source_bounded M domain(code_numeral M 1) ->context_bounded M b c l(succM M n) ->
 source_bounded M theta(succM M(succM M n)) ->source_bounded M first(succM M(succM M(succM M n))) ->
 source_bounded M second(succM M(succM M(succM M(succM M n)))) ->
 source_cutoff_shift M 1 theta first ->source_cutoff_shift M 1 first second ->source_cutoff_shift M 2 first second ->
 code_relation M(schema_env3 domain theta(zeroM M))(E_L_range_profile(CEvar 0)(CEvar 1)1)range ->
 code_relation M(schema_env3 domain(zeroM M)(zeroM M))(E_L_cover_witness(CEvar 0))bound ->
 code_relation M(schema_env3 domain second(zeroM M))(E_L_separation_law(CEvar 0)(CEvar 1))separation ->
 code_relation M(schema_env3 domain first(zeroM M))(E_L_cut_witness(CEvar 0)(CEvar 1))target ->
 source_full_prv M b c l range ->source_full_prv M b c l bound ->source_full_prv M b c l separation ->
 source_full_prv M b c l target.
Proof.
 intros HD HC HTheta HFirst HSecond H1 H2 H2' HR HB HS HT PR PB PS.
 assert(BTarget:source_bounded M target(succM M n)).
 { assert(B:schema_expression_bound M(schema_env3 domain first(zeroM M))
   (E_L_cut_witness(CEvar 0)(CEvar 1))(succM M n)).
   { unfold E_L_cut_witness,E_L_range_profile,E_sf_iff,E_sf_all,E_sf_ex,E_sf_mem. lrep_shell_bound. }
   exact(B target HT). }
 unfold E_L_cover_witness,E_sf_ex in HB.
 destruct(schema_expression_quantifier_split M _ SFEx _ bound HB)as(body&HBody&HEx).
 destruct(schema_expression_split M _ SFAnd _ _ body HBody)as(d&cover&HDCode&HCover&HAnd).
 change(d=domain)in HDCode. subst d.
 assert(BBody:source_bounded M body(succM M(succM M n))).
 { assert(B:schema_expression_bound M(schema_env3 domain(zeroM M)(zeroM M))
   (E_sf SFAnd(CEvar 0)(E_L_cover_profile(CEvar 0)))(succM M(succM M n))).
   { unfold E_L_cover_profile,E_sf_all,E_sf_mem. lrep_shell_bound. } exact(B body HBody). }
 destruct(context_shift_total M b c l)as(us&vs&HShift).
 destruct(environment_cons_total M us vs l body)as(ub&uc&un&HCons).
 assert(HBC:context_bounded M ub uc un(succM M(succM M n))).
 { apply(proj2(context_bounded_cons M us vs l body ub uc un _ HCons)).
   split;[exact BBody|exact(context_shift_preserves_bound M b c l us vs(succM M n)HShift HC)]. }
 assert(HIn:context_included M us vs l ub uc un).
 { intros f HF. apply(proj2(context_member_cons M us vs l body ub uc un f HCons));now right. }
 assert(PBody:source_full_prv M ub uc un body).
 { apply full_source_Ctx;[exists(succM M(succM M n));auto|].
   apply(proj2(context_member_cons M us vs l body ub uc un body HCons));now left. }
 pose proof(source_full_conjunction_left M ub uc un domain cover body HAnd PBody)as PD.
 pose proof(source_full_conjunction_right M ub uc un domain cover body HAnd PBody)as PC.
 destruct(code_relation_total M(E_L_range_profile(CEvar 0)(CEvar 1)2)(schema_env3 domain first(zeroM M)))as(range'&HR').
 pose proof(source_cutoff_zero_is_shift M range range'
  (source_L_range_profile_cutoff M 0 domain theta first 1 range range' HD H1 HR HR'))as HRShift.
 pose proof(source_full_prv_weaken_bounded M us vs l ub uc un range' _
  (source_full_prv_renaming M b c l range(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)us vs range' PR HShift HRShift)
   HIn HBC)as PR'.
 unfold E_L_separation_law,E_sf_all in HS.
 destruct(schema_expression_quantifier_split M _ SFAll _ separation HS)as(guarded&HGuarded&HAll).
 destruct(schema_expression_split M _ SFImpl _ _ guarded HGuarded)as(d&selection&HDCode&HSelection&HImp).
 change(d=domain)in HDCode. subst d.
 pose proof(source_full_prv_weaken_bounded M us vs l ub uc un guarded _
  (source_full_all_shift M b c l guarded separation us vs HAll PS HShift)HIn HBC)as PG.
 pose proof(source_full_modus_ponens M ub uc un domain selection guarded HImp PG PD)as PSelection.
 destruct(code_relation_total M(E_L_cut_witness(CEvar 0)(CEvar 1))(schema_env3 domain second(zeroM M)))as(shifted&HShiftedGraph).
 pose proof(source_L_cut_witness_shift M domain first second target shifted HD H2' HT HShiftedGraph)as HShifted.
 pose proof(source_full_L_cut_selection M domain first second range' cover selection shifted ub uc un n
   HD HBC HFirst HSecond H2 HR' HCover HSelection HShiftedGraph PR' PC PSelection)as PShifted.
 exact(full_source_ExE M b c l body bound target shifted us vs ub uc un
  (ex_intro _ (succM M n)(conj BTarget HC))PB PShifted HEx HShift HCons HShifted).
Qed.
Print Assumptions source_full_L_range_cut_by_bound.
