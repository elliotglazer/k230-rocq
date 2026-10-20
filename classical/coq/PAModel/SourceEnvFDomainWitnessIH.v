(** Relocate the actual induction proof past the three new successor roles.
    Only cutoff2 is used, so both leading witness names remain unchanged. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourceQuantifierRules
 SourceFiniteCutoffShift SourceCutoffShiftConstructors SourceCutoffPropositional NumericalRenaming
 SourceEnvFDomainGraph SourceEnvFDomainWitnessRecipe SourceEnvFDomainWitnessTransport SourceEnvFDomainWitnessMaps
 SourceEnvFDomainWitnessFixed SourceZFRProvability.
Unset Implicit Arguments.
Local Opaque ew_domain.
Theorem source_zfr_env_domain_witness_ih M p numeral old first second third shiftedThird inner target count:
 source_bounded M p(succM M count)->source_bounded M numeral(code_numeral M 1)->
 source_env_domain_witness_recipe M p numeral old->
 source_cutoff_shift M 1 p first->source_cutoff_shift M 1 first second->source_cutoff_shift M 1 second third->
 source_formula_shift M third shiftedThird->sf_relation M SFImpl numeral(ew_domain_code M 1 0)inner->
 sf_relation M SFImpl shiftedThird inner target->source_zfr_provable M old->source_zfr_provable M target.
Proof.
 intros BP BN(ps&dom&oldinner&HPS&HD&HInner&HOld)H1 H2 H3 HThird HIN HT POld.
 assert(ED:dom=ew_domain_code M 1 0).
 { exact(code_relation_functional M _ _ dom(ew_domain_code M 1 0)HD(source_env_domain_old_numeral M 1 0)). }
 subst dom. pose proof(sf_relation_functional M SFImpl numeral(ew_domain_code M 1 0)oldinner inner HInner HIN)as EI. subst oldinner.
 destruct(source_shift_cutoff_one_thrice M p first second third ps shiftedThird count BP H1 H2 H3 HPS HThird)as(s1&s2&HC1&HC2&HC3).
 pose proof(source_cutoff_shift_binary M 2 SFImpl numeral(ew_domain_code M 1 0)inner numeral(ew_domain_code M 1 0)inner
  (or_intror(or_intror eq_refl))HIN HIN(source_cutoff_shift_fixes_domain M 1 numeral BN)(source_env_domain_cutoff_two M _ HD))as HFixInner.
 destruct(sf_relation_total M SFImpl s1 inner)as(out1&HO1).
 destruct(sf_relation_total M SFImpl s2 inner)as(out2&HO2).
 pose proof(source_cutoff_shift_binary M 2 SFImpl ps inner old s1 inner out1(or_intror(or_intror eq_refl))HOld HO1 HC1 HFixInner)as HCOut1.
 pose proof(source_cutoff_shift_binary M 2 SFImpl s1 inner out1 s2 inner out2(or_intror(or_intror eq_refl))HO1 HO2 HC2 HFixInner)as HCOut2.
 pose proof(source_cutoff_shift_binary M 2 SFImpl s2 inner out2 shiftedThird inner target(or_intror(or_intror eq_refl))HO2 HT HC3 HFixInner)as HCOut3.
 exact(source_zfr_cutoff_proof M 2 out2 target HCOut3(source_zfr_cutoff_proof M 2 out1 out2 HCOut2(source_zfr_cutoff_proof M 2 old out1 HCOut1 POld))).
Qed.
Print Assumptions source_zfr_env_domain_witness_ih.
