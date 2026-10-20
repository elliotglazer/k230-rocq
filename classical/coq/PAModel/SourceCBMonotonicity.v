(** An actual Dn ordinal-monotonicity proof supplies the exact canonical
    monotonicity formula required by the CB successor. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
  NumericalRenamingMaps NumericalRenaming NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation RenamingSubstitution
  SourceSubstitutionIdentity SourceFixedSwap SourceQfRecipe SourceDomainInstances SourceOrdinalPredicate
  SourceFiniteCutoffShift SourceQuantifierRules SourceCBMonotoneMaps SourceCBMonotoneExchange SourceCBMonotoneCollapse
  SourceOrdinalUpperMembers SourceOrdinalMonotoneUse SourceSubsetSubstitution SourcePropositionalSubstitution
  SourcePropositionalTemplates SourceDescriptorClosure SourceDescriptorProvability SourceSetTheoryDescriptors SourceZFRProvability
  SourceNumeralLift.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code.

Lemma source_cb_subset_functional M x y a b:
  source_oc_subset_graph M x y a ->source_oc_subset_graph M x y b ->a=b.
Proof.
  intros(l&r&p&HL&HR&HP&HA)(l'&r'&p'&HL'&HR'&HP'&HB).
  pose proof(sf_relation_functional M SFMember(zeroM M)(succM M x)l l' HL HL') as E. subst l'.
  pose proof(sf_relation_functional M SFMember(zeroM M)(succM M y)r r' HR HR') as E. subst r'.
  pose proof(sf_relation_functional M SFImpl l r p p' HP HP') as E. subst p'.
  exact(sf_relation_functional M SFAll p(zeroM M)a b HA HB).
Qed.

Theorem source_cb_monotonicity_from_dn_law M dn q left right ordD subset point mono k:
  source_bounded M dn k ->
  numerical_renaming M dn(code_numeral M 210)(code_numeral M 6)(code_numeral M 3)(zeroM M)q ->
  source_formula_shift M dn left ->source_cutoff_shift M 1 dn right ->
  numerical_instantiation M(source_ordinal_predicate_code M)(code_numeral M 1)ordD ->
  source_oc_subset_graph M(code_numeral M 1)(zeroM M)subset ->
  code_relation M(source_oc_mono_environment ordD(source_ordinal_predicate_code M)subset left right)
    (source_prop_expression source_oc_mono_template)point ->
  source_descriptor_provable M ZFRSourceDescriptor point ->
  source_cb_monotonicity_graph M q mono ->source_zfr_provable M mono.
Proof.
  intros HB HQ HLeft HRight HOrd HSubset HPoint PPoint
    (left'&right'&ordD'&subset'&point'&inner&middle&HLeft'&HRight'&HOrd'&HSubset'&HPoint'&HI&HM&HO).
  pose proof(numerical_instantiation_functional M(source_ordinal_predicate_code M)(code_numeral M 1)
    ordD' ordD HOrd' HOrd) as E. subst ordD'.
  pose proof(source_cb_subset_functional M(code_numeral M 1)(zeroM M)subset' subset HSubset' HSubset) as E.
  subst subset'.
  destruct(source_cb_exchange_tail_total M) as(rb&rc&rn&HT).
  destruct(numerical_renaming_total M left rb rc rn(zeroM M)) as(l&HL).
  destruct(numerical_renaming_total M right rb rc rn(zeroM M)) as(r&HR).
  assert(HC0:source_cutoff_shift M 0 dn left).
  { exists(zeroM M),(zeroM M),(zeroM M). split;[repeat split;reflexivity|].
    apply(proj1(numerical_renaming_substitution M dn(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)left)) in HLeft.
    rewrite Arithmetic.add_zero in HLeft. exact HLeft. }
  pose proof(source_cb_dn_mono_matrix M false dn q left rb rc rn l k HB HQ HC0 HT HL) as HLM.
  pose proof(source_cb_dn_mono_matrix M true dn q right rb rc rn r k HB HQ HRight HT HR) as HRM.
  pose proof(numerical_renaming_functional M q _ _ _ _ l left' HLM HLeft') as E. subst l.
  pose proof(numerical_renaming_functional M q _ _ _ _ r right' HRM HRight') as E. subst r.
  assert(HLookup:forall i,(i<2)%nat ->
    substitution_lookup M rb rc rn(addM M rn(zeroM M))(code_numeral M i)(code_numeral M i)).
  { intros i HB'. apply(proj1(renaming_substitution_lookup M rb rc rn(zeroM M)_ _)).
    destruct i as[|[|i]];try lia.
    - exact(source_cb_exchange_tail_small M rb rc rn 0 HT ltac:(lia)).
    - exact(source_cb_exchange_tail_small M rb rc rn 1 HT ltac:(lia)). }
  assert(HFix:forall f,source_bounded M f(code_numeral M 2) ->
    numerical_substitution M f rb rc rn(addM M rn(zeroM M))f).
  { intros f HF. apply(numerical_substitution_identity_on_bound M f rb rc rn(addM M rn(zeroM M))(code_numeral M 2)HF).
    intros i HB'. destruct(source_numeral_initial_segment M 2 i HB') as(j&HJ&->). now apply HLookup. }
  assert(HOD:numerical_substitution M ordD rb rc rn(addM M rn(zeroM M))ordD).
  { apply HFix. exact(source_domain_instance_bound M(source_ordinal_predicate_code M)(code_numeral M 1)ordD
      (code_numeral M 2)(source_ordinal_predicate_bounded M)(coding_lt_succ M(code_numeral M 1))HOrd). }
  assert(HO0:numerical_substitution M(source_ordinal_predicate_code M)rb rc rn(addM M rn(zeroM M))
    (source_ordinal_predicate_code M)).
  { apply HFix. exact(SourceRelativizationBounds.sr_domain_bound_succ M(source_ordinal_predicate_code M)
      (code_numeral M 1)(source_ordinal_predicate_bounded M)). }
  pose proof(source_oc_subset_substitution M(code_numeral M 1)(zeroM M)subset(code_numeral M 1)(zeroM M)subset
    rb rc rn(addM M rn(zeroM M))HSubset(HLookup 1 ltac:(lia))(HLookup 0 ltac:(lia))HSubset) as HSS.
  assert(HRP:numerical_renaming M point rb rc rn(zeroM M)point').
  { apply(proj2(numerical_renaming_substitution M point rb rc rn(zeroM M)point')).
    apply(source_prop_expression_substitution M
      (source_oc_mono_environment ordD(source_ordinal_predicate_code M)subset left right)
      (source_oc_mono_environment ordD(source_ordinal_predicate_code M)subset left' right')
      rb rc rn(addM M rn(zeroM M))source_oc_mono_template);[|exact HPoint|exact HPoint'].
    intros[|[|[|[|i]]]];cbn[source_oc_mono_environment];try assumption.
    - exact(proj1(numerical_renaming_substitution M left rb rc rn(zeroM M)left')HL).
    - exact(proj1(numerical_renaming_substitution M right rb rc rn(zeroM M)right')HR). }
  pose proof(source_descriptor_provable_renaming M ZFRSourceDescriptor point rb rc rn(zeroM M)point' PPoint HRP) as PP.
  apply(proj1(source_zfr_descriptor_provable M mono)).
  apply(source_descriptor_provable_all M ZFRSourceDescriptor middle mono);[|exact HO].
  apply(source_descriptor_provable_all M ZFRSourceDescriptor inner middle);[|exact HM].
  exact(source_descriptor_provable_all M ZFRSourceDescriptor point' inner PP HI).
Qed.

Print Assumptions source_cb_monotonicity_from_dn_law.
