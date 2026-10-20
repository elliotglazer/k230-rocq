(** Actual two-ExE successor proof for the internally coded EnvF domain.
    Both predecessor witnesses are eliminated in the source calculus. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourceBoundMonotone
 SourceFiniteCutoffShift NumericalRenaming SourceQuantifierRules SourceDefinabilityStep SourceDefinabilityPrimitives
 SourceEnvFDomainWitnessRecipe SourceEnvFDomainWitnessTransport SourceEnvFDomainWitnessFixed SourceEnvFDomainWitnessMaps
 SourceEnvFDomainWitnessSyntax SourceEnvFDomainWitnessIH SourceEnvFDomainWitnessBounds SourceEnvFDomainWitnessPrograms
 SourceNumFUniqueSyntax SourceNumFClosureSyntax SourceWitnessProofComposition SourcePropositionalTemplates SourceZFRProvability SourceImplicationAllShift.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Local Opaque code_numeral source_def_successor01 numf_successor02 numf_successor03 ew_domain ew_extension032 ew_extension143.
Local Ltac ew_graph:=lazymatch goal with
 | |-code_relation ?M ?rho(source_prop_expression(SPTSlot ?idx))?out=>reflexivity
 | |-code_relation ?M ?rho(source_prop_expression(SPTImpl ?A ?B))?out=>
  match goal with H:sf_relation M SFImpl ?a ?b out|-_=>apply(source_prop_template_join M rho SFImpl A B a b out);[ew_graph|ew_graph|exact H]end
 | |-code_relation ?M ?rho(source_prop_expression(SPTAnd ?A ?B))?out=>
  match goal with H:sf_relation M SFAnd ?a ?b out|-_=>apply(source_prop_template_join M rho SFAnd A B a b out);[ew_graph|ew_graph|exact H]end
 end.
Theorem source_zfr_env_domain_witness_step M count p q envNext numNext old result:
 source_bounded M p(succM M count)->source_bounded M q(code_numeral M 1)->
 source_def_step M true p envNext->source_def_step M false q numNext->
 source_env_domain_witness_recipe M p q old->source_env_domain_witness_recipe M envNext numNext result->
 source_zfr_provable M old->source_zfr_provable M result.
Proof.
 intros BP BQ HEnv HNum HOld(es&dom&inner&HES&HD&HInner&HResult)POld.
 assert(ED:dom=ew_domain_code M 1 0).
 { exact(code_relation_functional M _ _ dom(ew_domain_code M 1 0)HD(source_env_domain_old_numeral M 1 0)). } subst dom.
 destruct(source_envf_witness_structure M p envNext HEnv)as(p1&p2&p3&shifted&envbody&shiftedBody&envShift&H1&H2&H3&HShifted&HEnvBody&HEnvEx&HEnvShift&HShiftedBody&HEnvBodyShift).
 pose proof(numerical_renaming_functional M envNext _ _ _ _ es envShift HES HEnvShift)as EE. subst es.
 destruct(source_numf_step_comparison_structure M q numNext BQ HNum)as(qs&pair&unused&numbody&unusedbody&q1&q2&
  HQS&HPair&HQ&HU&HPairShift&HNumBody&HNumEx&HQ1&HU2&HU3&HU4).
 set(K:=ew_role_bound M count).
 pose proof(source_cutoff_shift_bounded M 1 p p1 count BP H1)as BP1.
 pose proof(source_cutoff_shift_bounded M 1 p1 p2(succM M count)BP1 H2)as BP2.
 pose proof(source_cutoff_shift_bounded M 1 p2 p3(succM M(succM M count))BP2 H3)as BP3.
 pose proof(source_shift_bound M p3 shifted(succM M(succM M(succM M(succM M count))))BP3 HShifted)as BShifted.
 change(source_bounded M shifted K)in BShifted.
 pose proof(ew_raise_bound M p3 _ BP3)as BP3K. change(source_bounded M p3 K)in BP3K.
 pose proof(ew_fixed_bound M q 1 count ltac:(lia)BQ)as BQK.
 destruct(ew_extension_bounds M)as(BExt032&BExt143).
 pose proof(ew_fixed_bound M _ 4 count ltac:(lia)BExt032)as BExt032K.
 pose proof(ew_fixed_bound M _ 5 count ltac:(lia)BExt143)as BExt143K.
 pose proof(ew_fixed_bound M _ 5 count ltac:(lia)(ew_domain_fixed_bound M 1 0 ltac:(lia)ltac:(lia)))as BD10.
 pose proof(ew_fixed_bound M _ 5 count ltac:(lia)(ew_domain_fixed_bound M 2 1 ltac:(lia)ltac:(lia)))as BD21.
 pose proof(ew_fixed_bound M _ 5 count ltac:(lia)(ew_domain_fixed_bound M 3 2 ltac:(lia)ltac:(lia)))as BD32.
 pose proof(source_cutoff_shift_bounded M 1 _ _(code_numeral M 1)(numerical_def_successor_bound M)(proj1(source_numf_successor_cutoffs M)))as BS02.
 pose proof(ew_fixed_bound M _ 3 count ltac:(lia)BS02)as BS02K.
 destruct(sf_relation_total M SFImpl q(ew_domain_code M 1 0))as(oldinner&HOldInner).
 destruct(sf_relation_total M SFImpl shifted oldinner)as(ihlaw&HIH).
 pose proof(source_zfr_env_domain_witness_ih M p q old p1 p2 p3 shifted oldinner ihlaw count BP BQ HOld H1 H2 H3 HShifted HOldInner HIH POld)as PIH.
 destruct(source_zfr_ew_extension_shell M)as(fixedtail&fixedmiddle&fixed&HFT&HFM&HF&PFixed).
 destruct(sf_relation_total M SFImpl envbody(ew_domain_code M 2 1))as(target&Htarget).
 destruct(sf_relation_total M SFImpl shiftedBody(ew_domain_code M 3 2))as(shiftTarget&HshiftTarget).
 pose proof(source_implication_shift_graph M envbody(ew_domain_code M 2 1)target shiftedBody(ew_domain_code M 3 2)shiftTarget
  Htarget HshiftTarget HEnvBodyShift(ew_domain_shift M 2 1))as HTargetShift.
 destruct(sf_relation_total M SFImpl numbody shiftTarget)as(point&HPoint).
 set(rho:=fun idx:nat=>match idx with 0=>shifted|1=>q|2=>ew_domain_code M 1 0|3=>code_numeral M(sf_encode numf_successor02)|4=>code_numeral M(sf_encode ew_extension143)|_=>ew_domain_code M 3 2 end).
 assert(PPoint:source_zfr_provable M point).
 { apply(source_zfr_prop_two M ew_ih_template ew_fixed_template ew_point_template source_envf_domain_witness_point_program rho K ihlaw fixed point).
   - intros[|[|[|[|[|idx]]]]].
     + change(source_bounded M shifted K). exact BShifted.
     + change(source_bounded M q K). exact BQK.
     + change(source_bounded M(ew_domain_code M 1 0)K). exact BD10.
     + change(source_bounded M(code_numeral M(sf_encode numf_successor02))K). exact BS02K.
     + change(source_bounded M(code_numeral M(sf_encode ew_extension143))K). exact BExt143K.
     + change(source_bounded M(ew_domain_code M 3 2)K). exact BD32.
   - unfold ew_ih_template. ew_graph.
   - unfold ew_fixed_template. ew_graph.
   - unfold ew_point_template,ew_num_body,ew_env_body. ew_graph.
   - exact PIH.
   - exact PFixed. }
 pose proof(ew_binary_bound M p3 _ envbody K SFAnd(or_introl eq_refl)HEnvBody BP3K BExt032K)as BEnvBody.
 pose proof(ew_binary_bound M shifted _ shiftedBody K SFAnd(or_introl eq_refl)HShiftedBody BShifted BExt143K)as BShiftedBody.
 pose proof(ew_binary_bound M q _ numbody K SFAnd(or_introl eq_refl)HNumBody BQK BS02K)as BNumBody.
 pose proof(ew_exists_bound M numbody q1 K HNumEx BNumBody)as BQ1.
 pose proof(ew_binary_bound M envbody _ target K SFImpl(or_intror(or_intror eq_refl))Htarget BEnvBody BD21)as BTarget.
 destruct(sf_relation_total M SFImpl q1 target)as(mapnum&HMapNum).
 pose proof(source_zfr_exists_implication M numbody q1 target shiftTarget point mapnum K K BQ1 BTarget HNumEx HTargetShift HPoint HMapNum PPoint)as PMapNum.
 destruct(sf_relation_total M SFImpl q1(ew_domain_code M 2 1))as(innerShift&HInnerShift).
 destruct(sf_relation_total M SFImpl envbody innerShift)as(envpoint&HEnvPoint).
 set(srho:=fun idx:nat=>match idx with 0=>q1|1=>envbody|_=>ew_domain_code M 2 1 end).
 assert(PEnvPoint:source_zfr_provable M envpoint).
 { apply(source_zfr_prop_one M _ _ source_envf_domain_witness_reverse_program srho K mapnum envpoint).
   - intros[|[|idx]].
     + change(source_bounded M q1 K). exact BQ1.
     + change(source_bounded M envbody K). exact BEnvBody.
     + change(source_bounded M(ew_domain_code M 2 1)K). exact BD21.
   - ew_graph.
   - ew_graph.
   - exact PMapNum. }
 pose proof(source_implication_shift_graph M numNext(ew_domain_code M 1 0)inner q1(ew_domain_code M 2 1)innerShift
  HInner HInnerShift HQ1(ew_domain_shift M 1 0))as HInnerFullShift.
 pose proof(ew_exists_bound M envbody envShift K HEnvEx BEnvBody)as BEnvShift.
 pose proof(ew_fixed_bound M numNext 1 count ltac:(lia)(source_def_numeral_step_bound M q numNext BQ HNum))as BNumNext.
 pose proof(ew_binary_bound M numNext _ inner K SFImpl(or_intror(or_intror eq_refl))HInner BNumNext BD10)as BInner.
 exact(source_zfr_exists_implication M envbody envShift inner innerShift envpoint result K K
  BEnvShift BInner HEnvEx HInnerFullShift HEnvPoint HResult PEnvPoint).
Qed.
Print Assumptions source_zfr_env_domain_witness_step.

