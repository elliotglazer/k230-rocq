(** Actual ordinal monotonicity of Pc at arbitrary internal names. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 SourceBoundMonotone SourceD0Recipe SourceDn SourceDnBounds SourceDnOrdinalMonotonicity SourceThreeConditions
 SourceHierarchySyntax SourceOrdinalPredicate SourceRawSubset SourceRawSubsetBounds SourceDomainInstances
 SourceFiniteCutoffShift SourceQuantifierRules SourceDnCutoffDiamonds NumericalRenaming NumericalInstantiation
 NumericalSubstitution SourceUnarySubstitution SourceSubsetSubstitution SourcePropositionalSubstitution
 SourcePropositionalTemplates SourcePieceClosure SourceQfFunctionality SourcePieceMonotoneMaps SourceTripleSpecialization
 SourceDescriptorProvability SourceDescriptorClosure SourceSetTheoryDescriptors SourceZFRProvability SourceOrdinalMonotoneUse.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code.

Lemma source_three_curried_code M a b c d e law :source_three_curried M a b c d e law ->
 code_relation M(fun i=>match i with 0=>a|1=>b|2=>c|3=>d|_=>e end)
   (source_prop_expression source_three_curried_template)law.
Proof.
 intros(de&cde&bcde&HDE&HCD&HBC&HL). unfold source_three_curried_template.
 eapply source_prop_template_join;[reflexivity| |exact HL].
 eapply source_prop_template_join;[reflexivity| |exact HBC].
 eapply source_prop_template_join;[reflexivity| |exact HCD].
 eapply source_prop_template_join;[reflexivity|reflexivity|exact HDE].
Qed.

Theorem source_zfr_pc_monotonicity M domain level count phi d e X od oe subset pcD pcE law :
 source_bounded M domain(code_numeral M 1) ->source_bounded M phi(succM M count) ->
 source_LL_instance M(code_numeral M 1)(zeroM M)level ->
 numerical_instantiation M(source_ordinal_predicate_code M)d od ->
 numerical_instantiation M(source_ordinal_predicate_code M)e oe ->source_raw_subset_graph M d e subset ->
 source_pc_instance M domain level count phi d X pcD ->source_pc_instance M domain level count phi e X pcE ->
 source_three_curried M od oe subset pcD pcE law ->source_zfr_provable M law.
Proof.
 intros HD HB HL HOD HOE HS(d0&dn&rb&rc&H0&HN&HR&HPD)(d0'&dn'&ub&uc&H0'&HN'&HU&HPE)HNamed.
 pose proof(source_d0_recipe_functional M domain level phi d0' d0 H0' H0) as E. subst d0'.
 pose proof(source_dn_functional M count d0 dn' dn HN' HN) as E. subst dn'.
 pose proof(source_LL_instance_bounded M(code_numeral M 1)(zeroM M)level(code_numeral M 2)
   (coding_lt_succ M(code_numeral M 1))(coding_zero_lt_succ M(code_numeral M 1))HL) as BL.
 pose proof(source_pc_dn_bounded M domain level count phi d0 dn HD BL HB H0 HN) as BDN.
 assert(B0:source_bounded M d0(addM M count(code_numeral M 2))).
 { change(source_bounded M d0(addM M count(succM M(succM M(zeroM M))))). rewrite Arithmetic.add_comm,!Arithmetic.add_succ,Arithmetic.add_zero.
   exact(source_d0_recipe_bounded M domain level phi d0 count HD BL HB H0). }
 destruct(source_cutoff_shift_total M 0 dn) as(da&HDA0).
 pose proof(proj2(source_formula_shift_cutoff_zero M dn da)HDA0) as HDA.
 destruct(source_cutoff_shift_total M 1 dn) as(db&HDB).
 destruct(numerical_instantiation_total M(source_ordinal_predicate_code M)(code_numeral M 1)) as(rawD&HRawD).
 destruct(source_raw_subset_total M(code_numeral M 1)(zeroM M)) as(rawSub&HRawSub).
 destruct(sf_relation_total M SFImpl da db) as(map&HMap).
 destruct(sf_relation_total M SFImpl rawSub map) as(t2&HT2).
 destruct(sf_relation_total M SFImpl(source_ordinal_predicate_code M)t2) as(t1&HT1).
 destruct(sf_relation_total M SFImpl rawD t1) as(point&HPoint).
 assert(HCurried:source_three_curried M rawD(source_ordinal_predicate_code M)rawSub da db point) by(exists map,t2,t1;auto).
 pose proof(source_zfr_dn_ordinal_monotonicity M domain level phi count d0 dn da db rawD
   (source_ordinal_predicate_code M)rawSub point count(zeroM M)HD HB B0 HL H0 HN HDA HDB HRawD
   (source_domain_instance_zero M(source_ordinal_predicate_code M)(source_ordinal_predicate_bounded M))HRawSub HCurried) as PP.
 destruct(sf_relation_total M SFAll point(zeroM M)) as(inner&HI).
 destruct(sf_relation_total M SFAll inner(zeroM M)) as(middle&HM).
 destruct(sf_relation_total M SFAll middle(zeroM M)) as(outer&HO).
 pose proof(source_descriptor_provable_all M ZFRSourceDescriptor point inner
   (proj2(source_zfr_descriptor_provable M point)PP)HI) as PInner.
 pose proof(source_descriptor_provable_all M ZFRSourceDescriptor inner middle PInner HM) as PMiddle.
 destruct(source_descriptor_provable_all M ZFRSourceDescriptor middle outer PMiddle HO) as(b&c&n&HContext&POuter).
 destruct(source_triple_prefix_total M e d X) as(tb&tc&HTriple).
 pose proof(source_pc_cutoff_specialization M false dn da d e X tb tc rb rc pcD BDN HDA0 HTriple HR HPD) as HSD.
 pose proof(source_pc_cutoff_specialization M true dn db d e X tb tc ub uc pcE BDN HDB HTriple HU HPE) as HSE.
 pose proof(source_domain_instance_substitution_graph M(source_ordinal_predicate_code M)(code_numeral M 1)rawD
   tb tc(code_numeral M 3)(zeroM M)d od(source_ordinal_predicate_bounded M)HRawD(proj1(proj2 HTriple))HOD) as HOrdD.
 pose proof(source_domain_instance_substitution_graph M(source_ordinal_predicate_code M)(zeroM M)(source_ordinal_predicate_code M)
   tb tc(code_numeral M 3)(zeroM M)e oe(source_ordinal_predicate_bounded M)
   (source_domain_instance_zero M(source_ordinal_predicate_code M)(source_ordinal_predicate_bounded M))(proj1 HTriple)HOE) as HOrdE.
 pose proof(source_oc_subset_substitution M(code_numeral M 1)(zeroM M)rawSub d e subset
   tb tc(code_numeral M 3)(zeroM M)HRawSub(proj1(proj2 HTriple))(proj1 HTriple)HS) as HSubset.
 assert(HSub:numerical_substitution M point tb tc(code_numeral M 3)(zeroM M)law).
 { apply(source_prop_expression_substitution M
     (fun i=>match i with 0=>rawD|1=>source_ordinal_predicate_code M|2=>rawSub|3=>da|_=>db end)
     (fun i=>match i with 0=>od|1=>oe|2=>subset|3=>pcD|_=>pcE end)
     tb tc(code_numeral M 3)(zeroM M)source_three_curried_template).
   - intros[|[|[|[|i]]]];assumption.
   - exact(source_three_curried_code M _ _ _ _ _ point HCurried).
   - exact(source_three_curried_code M _ _ _ _ _ law HNamed). }
 pose proof(source_cutoff_shift_bounded M 0 dn da(code_numeral M 2)BDN HDA0) as BDA.
 pose proof(source_cutoff_shift_bounded M 1 dn db(code_numeral M 1)BDN HDB) as BDB.
 pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)(code_numeral M 1)rawD(code_numeral M 3)
   (source_ordinal_predicate_bounded M)ltac:(apply coding_lt_succ_cancel,coding_zero_lt_succ)HRawD) as BOD.
 pose proof(source_bounded_monotone M(source_ordinal_predicate_code M)(code_numeral M 1)(code_numeral M 3)
   (source_ordinal_predicate_bounded M)ltac:(apply coding_lt_succ_cancel,coding_zero_lt_succ)) as BOE.
 pose proof(source_raw_subset_bounded M(code_numeral M 1)(zeroM M)rawSub(code_numeral M 3)
   ltac:(apply coding_lt_succ_cancel,coding_zero_lt_succ)(coding_zero_lt_succ M(code_numeral M 2))HRawSub) as BS.
 pose proof(source_prop_template_bound M (fun i=>match i with 0=>rawD|1=>source_ordinal_predicate_code M|2=>rawSub|3=>da|_=>db end) source_three_curried_template(code_numeral M 3)
   ltac:(intros[|[|[|[|i]]]];assumption)point(source_three_curried_code M _ _ _ _ _ point HCurried)) as BPoint.
 exists b,c,n. split;[exact(proj1(source_zfr_descriptor_context M b c n)HContext)|].
 exact(source_full_triple_specialize M b c n point inner middle outer X d e tb tc law(code_numeral M 3)
   BPoint HI HM HO HTriple HSub POuter).
Qed.

Print Assumptions source_zfr_pc_monotonicity.
