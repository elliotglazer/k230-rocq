(** A covering L-level and relative Separation suffice to replace a raw
    range profile by an L-output profile. The output witness is unchanged
    by the pointwise cut; all three universal profiles share their matrix. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SetSchemaConstructors SchemaConstructorBounds SourceBounded
 NumericalContexts NumericalRenaming NumericalContextRenaming NumericalEnvironments NumericalSourceFull SourceTraceBounds SourceProofWeakening SourceProofRenaming
 SourceContextTransport SourceConjunctionRules SourceDerivedRules SourceNamedProofRules SourceQuantifierRules SourceExistentialMap
 SourceRelativizationBounds SourceUniversalPropositional SourcePropositionalTemplates SourcePropositionalRebase SourceBooleanIffPrograms
 SourceWFSeparationConstructor SourceWFReplacementProfileGraphs SourceCutoffShiftConstructors SourceCutoffQuantifiers SourceCutoffPropositional
 SourceLReplacementCutProfile SourceLReplacementCutShells SourceFiniteCutoffShift.
Unset Implicit Arguments.
Definition E_L_cover_profile_shifted d:=E_sf_all(E_sf SFImpl(E_sf_mem 0 3)(E_sf SFImpl d(E_sf_mem 0 2))).
Theorem source_L_cover_profile_shift M domain a b:
 source_bounded M domain(code_numeral M 1) ->
 code_relation M(schema_env3 domain(zeroM M)(zeroM M))(E_L_cover_profile(CEvar 0))a ->
 code_relation M(schema_env3 domain(zeroM M)(zeroM M))(E_L_cover_profile_shifted(CEvar 0))b ->source_formula_shift M a b.
Proof.
 intros HD HA HB. unfold E_L_cover_profile,E_L_cover_profile_shifted,E_sf_all in HA,HB.
 destruct(schema_expression_quantifier_split M _ SFAll _ a HA)as(p&HP&HAllA).
 destruct(schema_expression_quantifier_split M _ SFAll _ b HB)as(q&HQ&HAllB).
 destruct(schema_expression_split M _ SFImpl _ _ p HP)as(ma&ta&HMA&HTA&HPA).
 destruct(schema_expression_split M _ SFImpl _ _ q HQ)as(mb&tb&HMB&HTB&HQA).
 destruct(schema_expression_split M _ SFImpl _ _ ta HTA)as(d&na&HDa&HNA&HIA).
 destruct(schema_expression_split M _ SFImpl _ _ tb HTB)as(d'&nb&HDb&HNB&HIB).
 change(d=domain)in HDa. change(d'=domain)in HDb. subst d d'.
 pose proof(source_cutoff_shift_fixed_member M 1 0 2 ma mb HMA HMB)as HM.
 pose proof(source_cutoff_shift_fixed_member M 1 0 1 na nb HNA HNB)as HN.
 assert(HT:source_cutoff_shift M 1 ta tb).
 { eapply source_cutoff_shift_binary;[right;right;reflexivity|exact HIA|exact HIB|
 exact(source_cutoff_shift_fixes_domain M 0 domain HD)|exact HN]. }
 apply source_cutoff_zero_is_shift. apply(source_cutoff_quantifier_join M 0 true p q a b HAllA HAllB).
 eapply source_cutoff_shift_binary;[right;right;reflexivity|exact HPA|exact HQA|exact HM|exact HT].
Qed.
Ltac lrep_shell_bound:=
 repeat schema_constructor_bound;try schema_small_index;cbn[schema_env3];try assumption;
 apply sr_domain_bound_succ;assumption.
Theorem source_full_L_cut_selection M domain theta final range cover selection target b c l n:
 source_bounded M domain(code_numeral M 1) ->context_bounded M b c l(succM M(succM M n)) ->
 source_bounded M theta(succM M(succM M(succM M n))) ->
 source_bounded M final(succM M(succM M(succM M(succM M n)))) ->source_cutoff_shift M 1 theta final ->
 code_relation M(schema_env3 domain theta(zeroM M))(E_L_range_profile(CEvar 0)(CEvar 1)2)range ->
 code_relation M(schema_env3 domain(zeroM M)(zeroM M))(E_L_cover_profile(CEvar 0))cover ->
 code_relation M(schema_env3 domain final(zeroM M))(E_L_selection_witness(CEvar 0)(CEvar 1))selection ->
 code_relation M(schema_env3 domain final(zeroM M))(E_L_cut_witness(CEvar 0)(CEvar 1))target ->
 source_full_prv M b c l range ->source_full_prv M b c l cover ->source_full_prv M b c l selection ->
 source_full_prv M b c l target.
Proof.
 intros HD HC HTheta HFinal HT HR HCover HSelection HTarget PR PC PS.
 set(env:=schema_env3 domain final(zeroM M)).
 assert(BTarget:source_bounded M target(succM M(succM M n))).
 { assert(B:schema_expression_bound M env(E_L_cut_witness(CEvar 0)(CEvar 1))(succM M(succM M n))).
   { unfold E_L_cut_witness,E_L_range_profile,E_sf_iff,E_sf_all,E_sf_ex,E_sf_mem. lrep_shell_bound. }
   exact(B target HTarget). }
 unfold E_L_selection_witness,E_L_cut_witness,E_sf_ex in HSelection,HTarget.
 destruct(schema_expression_quantifier_split M _ SFEx _ selection HSelection)as(sb&HSB&HSE).
 destruct(schema_expression_quantifier_split M _ SFEx _ target HTarget)as(tb&HTB&HTE).
 destruct(schema_expression_split M _ SFAnd _ _ sb HSB)as(d&allS&HDS&HAllS&HSAnd).
 destruct(schema_expression_split M _ SFAnd _ _ tb HTB)as(d'&allT&HDT&HAllT&HTAnd).
 change(d=domain)in HDS. change(d'=domain)in HDT. subst d d'.
 assert(BSB:source_bounded M sb(succM M(succM M(succM M n)))).
 { assert(B:schema_expression_bound M env(E_sf SFAnd(CEvar 0)
   (E_sf_all(E_sf SFImpl(CEvar 0)(E_sf_iff(E_sf_mem 0 1)(E_sf SFAnd(E_sf_mem 0 2)(CEvar 1))))))
    (succM M(succM M(succM M n)))).
   { unfold E_sf_iff,E_sf_all,E_sf_mem. lrep_shell_bound. } exact(B sb HSB). }
 destruct(context_shift_total M b c l)as(us&vs&HShift).
 destruct(environment_cons_total M us vs l sb)as(ub&uc&un&HCons).
 assert(HBC:context_bounded M ub uc un(succM M(succM M(succM M n)))).
 { apply(proj2(context_bounded_cons M us vs l sb ub uc un _ HCons)).
   split;[exact BSB|exact(context_shift_preserves_bound M b c l us vs(succM M(succM M n))HShift HC)]. }
 assert(HIn:context_included M us vs l ub uc un).
 { intros f HF. apply(proj2(context_member_cons M us vs l sb ub uc un f HCons));now right. }
 assert(PSB:source_full_prv M ub uc un sb).
 { apply full_source_Ctx;[exists(succM M(succM M(succM M n)));auto|].
   apply(proj2(context_member_cons M us vs l sb ub uc un sb HCons));now left. }
 pose proof(source_full_conjunction_left M ub uc un domain allS sb HSAnd PSB)as PD.
 pose proof(source_full_conjunction_right M ub uc un domain allS sb HSAnd PSB)as PAS.
 destruct(code_relation_total M(E_L_range_profile(CEvar 0)(CEvar 1)3)env)as(newRange&HNewRange).
 pose proof(source_cutoff_zero_is_shift M range newRange
  (source_L_range_profile_cutoff M 0 domain theta final 2 range newRange HD HT HR HNewRange))as HRangeShift.
 pose proof(source_full_prv_weaken_bounded M us vs l ub uc un newRange _
  (source_full_prv_renaming M b c l range(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)us vs newRange PR HShift HRangeShift)
   HIn HBC)as PNR.
 destruct(code_relation_total M(E_L_cover_profile_shifted(CEvar 0))(schema_env3 domain(zeroM M)(zeroM M)))as(newCover&HNewCover).
 pose proof(source_L_cover_profile_shift M domain cover newCover HD HCover HNewCover)as HCoverShift.
 pose proof(source_full_prv_weaken_bounded M us vs l ub uc un newCover _
  (source_full_prv_renaming M b c l cover(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)us vs newCover PC HShift HCoverShift)
   HIn HBC)as PNC.
 destruct(code_relation_total M(E_sf_mem 0 3)env)as(mz&HMZ).
 destruct(code_relation_total M(E_sf_mem 0 2)env)as(my&HMY).
 destruct(code_relation_total M(E_sf_mem 0 1)env)as(mb&HMB).
 set(rho:=fun i=>match i with 0=>domain|1=>mz|2=>my|3=>mb|_=>final end).
 set(holes:=fun i=>match i with 0=>CEvar 0|1=>E_sf_mem 0 3|2=>E_sf_mem 0 2|3=>E_sf_mem 0 1|_=>CEvar 1 end).
 assert(HH:forall i,code_relation M env(holes i)(rho i)).
 { intros[|[|[|[|i]]]];cbn[holes rho];try reflexivity;assumption. }
 assert(HRB:forall i,source_bounded M(rho i)(succM M(succM M(succM M(succM M n))))).
 { intros[|[|[|[|i]]]];cbn[rho].
   - exact(sr_domain_bound_succ M domain(succM M(succM M(succM M n)))HD).
   - apply(proj2(source_bounded_accept_atom M SFMember(zeroM M)(code_numeral M 3)mz
       (succM M(succM M(succM M(succM M n))))(or_introl eq_refl)HMZ));split;schema_small_index.
   - apply(proj2(source_bounded_accept_atom M SFMember(zeroM M)(code_numeral M 2)my
       (succM M(succM M(succM M(succM M n))))(or_introl eq_refl)HMY));split;schema_small_index.
   - apply(proj2(source_bounded_accept_atom M SFMember(zeroM M)(code_numeral M 1)mb
       (succM M(succM M(succM M(succM M n))))(or_introl eq_refl)HMB));split;schema_small_index.
   - exact HFinal. } unfold E_L_range_profile,E_sf_all in HNewRange,HAllT.
 unfold E_L_cover_profile_shifted,E_sf_all in HNewCover.
 destruct(schema_expression_quantifier_split M _ SFAll _ newRange HNewRange)as(rp&HRP&HRAll).
 destruct(schema_expression_quantifier_split M _ SFAll _ newCover HNewCover)as(cp&HCP&HCAll).
 destruct(schema_expression_quantifier_split M _ SFAll _ allS HAllS)as(sp&HSP&HSAll).
 destruct(schema_expression_quantifier_split M _ SFAll _ allT HAllT)as(tp&HTP&HTAll).
 assert(HRP':code_relation M rho(source_prop_expression lrep_range_point)rp).
 { apply(proj1(source_prop_expression_with_graph M env holes rho lrep_range_point HH rp));exact HRP. }
 assert(HCP':code_relation M rho(source_prop_expression lrep_cover_point)cp).
 { apply(proj1(source_prop_expression_with_graph M env holes rho lrep_cover_point HH cp));exact HCP. }
 assert(HSP':code_relation M rho(source_prop_expression lrep_selection_point)sp).
 { apply(proj1(source_prop_expression_with_graph M env holes rho lrep_selection_point HH sp));exact HSP. }
 assert(HTP':code_relation M rho(source_prop_expression lrep_cut_point)tp).
 { apply(proj1(source_prop_expression_with_graph M env holes rho lrep_cut_point HH tp));exact HTP. }
 pose proof(source_full_L_replacement_cut_profile M rho(succM M(succM M(succM M n)))ub uc un
  rp cp sp tp newRange newCover allS allT HRB HBC HRP' HCP' HSP' HTP' HRAll HCAll HSAll HTAll PNR PNC PAS)as PAT.
 pose proof(source_full_and_intro M ub uc un domain allT tb HTAnd PD PAT)as PTB.
 destruct(numerical_renaming_total M target(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1))as(shifted&HShifted).
 exact(source_full_exists_map M b c l sb tb selection target us vs ub uc un shifted
  (ex_intro _ (succM M(succM M n))(conj BTarget HC))HSE HTE HShift HCons HShifted PS PTB).
Qed.
Print Assumptions source_L_cover_profile_shift.
Print Assumptions source_full_L_cut_selection.




