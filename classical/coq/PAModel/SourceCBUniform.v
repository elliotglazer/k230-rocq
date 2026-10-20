(** Uniform bounded collection over an internally arbitrary number of
    parameters. Every conclusion is an actual numerical ZFR derivation. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions NumericalProofs
  SetFormulaCodes SourceBounded NumericalRenaming NumericalInstantiation SourceFiniteCutoffShift
  SourceLFixed SourceHierarchySyntax SourceOrdinalPredicate SourceDomainInstances SourceRawSubset
  SourceD0Recipe SourceDn SourceDnBounds SourceDnOrdinalMonotonicity SourceThreeConditions
  SourceQfRecipe SourceCBGoal SourceCBProofProperty SourceCBMonotoneCollapse SourceCBMonotonicity
  SourceCBGraphs SourceCBSuccessor SourcePropositionalTemplates SourceOrdinalMonotoneUse SourceFunctionalityShells
  SourceDescriptorProvability SourceSetTheoryDescriptors SourceZFRProvability.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code source_L_domain_code.

Theorem source_zfr_cb_monotonicity M level count phi q mono n:
  source_LL_instance M(code_numeral M 1)(zeroM M)level ->
  source_bounded M phi(addM M count(succM M(succM M n))) ->
  source_qf_recipe M(source_L_domain_code M)level count phi q ->
  source_cb_monotonicity_graph M q mono ->source_zfr_provable M mono.
Proof.
  intros HL HB(d0&dn&HD0&HDN&HQ)HMono.
  assert(HB':source_bounded M phi(succM M(addM M count(succM M n)))).
  { now rewrite <-qf_add_succ_right. }
  pose proof(source_LL_instance_bounded M(code_numeral M 1)(zeroM M)level(code_numeral M 2)
    (coding_lt_succ M(code_numeral M 1))(coding_zero_lt_succ M(code_numeral M 1))HL) as HLevelB.
  pose proof(source_d0_recipe_bounded M(source_L_domain_code M)level phi d0(addM M count(succM M n))
    (numerical_L_domain_bounded M)HLevelB HB' HD0) as HBD0.
  assert(HBD0':source_bounded M d0(addM M count(succM M(succM M(succM M n))))).
  { now rewrite <-qf_add_succ_right,<-qf_add_succ_right in HBD0. }
  pose proof(source_dn_bounded M count d0 dn(succM M n)HDN HBD0') as HBDN.
  destruct(numerical_renaming_total M dn(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)) as(da&HDA).
  destruct(source_cutoff_shift_total M 1 dn) as(db&HDB).
  destruct(numerical_instantiation_total M(source_ordinal_predicate_code M)(code_numeral M 1)) as(od&HOD).
  destruct(source_raw_subset_total M(code_numeral M 1)(zeroM M)) as(subset&HSubset).
  destruct(sf_relation_total M SFImpl da db) as(map&HMap).
  destruct(sf_relation_total M SFImpl subset map) as(tail2&HTail2).
  destruct(sf_relation_total M SFImpl(source_ordinal_predicate_code M)tail2) as(tail1&HTail1).
  destruct(sf_relation_total M SFImpl od tail1) as(law&HLaw).
  assert(HCurried:source_three_curried M od(source_ordinal_predicate_code M)subset da db law).
  { exists map,tail2,tail1. auto. }
  pose proof(source_zfr_dn_ordinal_monotonicity M(source_L_domain_code M)level phi count d0 dn da db od
    (source_ordinal_predicate_code M)subset law(addM M count(succM M n))(succM M n)
    (numerical_L_domain_bounded M)HB' HBD0' HL HD0 HDN HDA HDB HOD
    (source_domain_instance_zero M(source_ordinal_predicate_code M)(source_ordinal_predicate_bounded M))
    HSubset HCurried) as PLaw.
  assert(HLawGraph:code_relation M(source_oc_mono_environment od(source_ordinal_predicate_code M)subset da db)
    (source_prop_expression source_oc_mono_template)law).
  { unfold source_oc_mono_template,source_prop_expression. functionality_graph. }
  exact(source_cb_monotonicity_from_dn_law M dn q da db od subset law mono
    (succM M(succM M(succM M n)))HBDN HQ HDA HDB HOD HSubset HLawGraph
    (proj2(source_zfr_descriptor_provable M law)PLaw)HMono).
Qed.

Theorem source_cb_proof_successor M level count:
  source_LL_instance M(code_numeral M 1)(zeroM M)level ->
  source_cb_proof_at M(source_L_domain_code M)level(source_ordinal_predicate_code M)count ->
  source_cb_proof_at M(source_L_domain_code M)level(source_ordinal_predicate_code M)(succM M count).
Proof.
  intros HL IH phi n g ordinal goal implication HB HG HOrdinal HGoal HImp.
  assert(HB':source_bounded M phi(addM M count(succM M(succM M n)))).
  { rewrite Arithmetic.add_succ,<-qf_add_succ_right in HB. exact HB. }
  destruct(source_qf_recipe_total M(source_L_domain_code M)level count phi) as(q&HQ).
  pose proof(source_LL_instance_bounded M(code_numeral M 1)(zeroM M)level(code_numeral M 2)
    (coding_lt_succ M(code_numeral M 1))(coding_zero_lt_succ M(code_numeral M 1))HL) as HLevelB.
  pose proof(source_qf_recipe_bounded M(source_L_domain_code M)level count phi q n
    (numerical_L_domain_bounded M)HLevelB HB' HQ) as HQB.
  destruct(source_cb_monotonicity_total M q(succM M(succM M(succM M n)))HQB) as(mono&HMono).
  pose proof(source_zfr_cb_monotonicity M level count phi q mono n HL HB' HQ HMono) as PMono.
  apply(proj2(source_zfr_descriptor_provable M implication)).
  exact(source_cb_successor_use M level count phi q mono g ordinal goal implication n
    HL IH HB' HQ HMono PMono HG HOrdinal HGoal HImp).
Qed.

Theorem source_cb_proof_all M level:
  source_LL_instance M(code_numeral M 1)(zeroM M)level ->
  forall count,source_cb_proof_at M(source_L_domain_code M)level(source_ordinal_predicate_code M)count.
Proof.
  intro HL. apply(definable_induction M
    (source_cb_proof_at M(source_L_domain_code M)level(source_ordinal_predicate_code M))
    (source_cb_proof_definable M(source_L_domain_code M)level(source_ordinal_predicate_code M))).
  - exact(source_cb_proof_zero M level HL).
  - intros count IH. exact(source_cb_proof_successor M level count HL IH).
Qed.

Theorem source_zfr_cb_uniform M level count phi g ordinal goal implication n:
  source_LL_instance M(code_numeral M 1)(zeroM M)level ->
  source_bounded M phi(addM M count(succM M n)) ->coding_lt M g(succM M n) ->
  numerical_instantiation M(source_ordinal_predicate_code M)g ordinal ->
  source_cb_goal M(source_L_domain_code M)level(source_ordinal_predicate_code M)count phi goal ->
  sf_relation M SFImpl ordinal goal implication ->source_zfr_provable M implication.
Proof.
  intros HL HB HG HOrd HGoal HImp. apply(proj1(source_zfr_descriptor_provable M implication)).
  exact(source_cb_proof_all M level HL count phi n g ordinal goal implication HB HG HOrd HGoal HImp).
Qed.

Print Assumptions source_zfr_cb_monotonicity.
Print Assumptions source_cb_proof_successor.
Print Assumptions source_cb_proof_all.
Print Assumptions source_zfr_cb_uniform.
