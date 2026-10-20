(** Raw-range existential elimination. The strong covering-set law is
    an actual theorem in a closed base; Separation is an ordinary source
    deduction. No varying witness-existence promise is used. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SetSchemaConstructors SchemaConstructorBounds SourceBounded
 NumericalContexts NumericalContextRenaming NumericalEnvironments NumericalRenaming NumericalSourceFull SourceTraceBounds SourceProofWeakening SourceProofRenaming
 SourceContextTransport SourceClosedContextShift SourceConjunctionRules SourceDerivedRules SourceQuantifierRules SourceExistentialMap
 SourceRelativizationBounds SourcePropositionalRebase SourceWFSeparationConstructor
 SourceLReplacementCutShells SourceLReplacementCutSelection SourceLReplacementBoundCut SourceFiniteCutoffShift.
Unset Implicit Arguments.
Theorem source_full_L_range_cut M domain theta first second rawrange bound separation shiftedSeparation target
 b c l fb fc fn n:
 source_bounded M domain(code_numeral M 1) ->context_bounded M b c l n ->
 context_bounded M fb fc fn(zeroM M) ->context_included M fb fc fn b c l ->
 source_bounded M theta(succM M(succM M n)) ->source_bounded M first(succM M(succM M(succM M n))) ->
 source_bounded M second(succM M(succM M(succM M(succM M n)))) ->
 source_cutoff_shift M 1 theta first ->source_cutoff_shift M 2 theta first ->
 source_cutoff_shift M 1 first second ->source_cutoff_shift M 2 first second ->
 code_relation M(schema_env3 domain theta(zeroM M))(E_sf_ex(E_L_range_profile(CEvar 0)(CEvar 1)1))rawrange ->
 code_relation M(schema_env3 domain(zeroM M)(zeroM M))(E_L_cover_witness(CEvar 0))bound ->
 code_relation M(schema_env3 domain second(zeroM M))(E_L_separation_law(CEvar 0)(CEvar 1))shiftedSeparation ->
 source_formula_shift M separation shiftedSeparation ->
 code_relation M(schema_env3 domain theta(zeroM M))(E_L_cut_witness(CEvar 0)(CEvar 1))target ->
 source_full_prv M fb fc fn bound ->source_full_prv M b c l separation ->source_full_prv M b c l rawrange ->
 source_full_prv M b c l target.
Proof.
 intros HD HC HFC HFI HTheta HFirst HSecond H1 H1' H2 H2' HR HB HSS HShiftSep HT PB PS PR.
 assert(BTarget:source_bounded M target n).
 { assert(B:schema_expression_bound M(schema_env3 domain theta(zeroM M))
   (E_L_cut_witness(CEvar 0)(CEvar 1))n).
   { unfold E_L_cut_witness,E_L_range_profile,E_sf_iff,E_sf_all,E_sf_ex,E_sf_mem. lrep_shell_bound. }
   exact(B target HT). }
 unfold E_sf_ex in HR.
 destruct(schema_expression_quantifier_split M _ SFEx _ rawrange HR)as(profile&HProfile&HEx).
 assert(BProfile:source_bounded M profile(succM M n)).
 { assert(B:schema_expression_bound M(schema_env3 domain theta(zeroM M))
   (E_L_range_profile(CEvar 0)(CEvar 1)1)(succM M n)).
   { unfold E_L_range_profile,E_sf_iff,E_sf_all,E_sf_mem. lrep_shell_bound. }
   exact(B profile HProfile). }
 destruct(context_shift_total M b c l)as(us&vs&HShift).
 destruct(environment_cons_total M us vs l profile)as(ub&uc&un&HCons).
 assert(HBC:context_bounded M ub uc un(succM M n)).
 { apply(proj2(context_bounded_cons M us vs l profile ub uc un _ HCons)).
   split;[exact BProfile|exact(context_shift_preserves_bound M b c l us vs n HShift HC)]. }
 assert(HIn:context_included M us vs l ub uc un).
 { intros f HF. apply(proj2(context_member_cons M us vs l profile ub uc un f HCons));now right. }
 assert(HFIn:context_included M fb fc fn ub uc un).
 { intros f HF. apply HIn. exact(source_context_included_shift M fb fc fn b c l fb fc us vs HFI
     (source_closed_context_shift_self M fb fc fn HFC)HShift f HF). }
 pose proof(source_full_prv_weaken_bounded M fb fc fn ub uc un bound(succM M n)PB HFIn HBC)as PB'.
 pose proof(source_full_prv_weaken_bounded M us vs l ub uc un shiftedSeparation(succM M n)
  (source_full_prv_renaming M b c l separation(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)
    us vs shiftedSeparation PS HShift HShiftSep)HIn HBC)as PS'.
 assert(PProfile:source_full_prv M ub uc un profile).
 { apply full_source_Ctx;[exists(succM M n);auto|].
   apply(proj2(context_member_cons M us vs l profile ub uc un profile HCons));now left. }
 destruct(code_relation_total M(E_L_cut_witness(CEvar 0)(CEvar 1))(schema_env3 domain first(zeroM M)))as(shifted&HSGraph).
 pose proof(source_L_cut_witness_shift M domain theta first target shifted HD H1' HT HSGraph)as HShifted.
 pose proof(source_full_L_range_cut_by_bound M domain theta first second profile bound shiftedSeparation shifted
   ub uc un n HD HBC HTheta HFirst HSecond H1 H2 H2' HProfile HB HSS HSGraph PProfile PB' PS')as PShifted.
 exact(full_source_ExE M b c l profile rawrange target shifted us vs ub uc un
  (ex_intro _ n(conj BTarget HC))PR PShifted HEx HShift HCons HShifted).
Qed.
Print Assumptions source_full_L_range_cut.
