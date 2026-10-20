(** Unconditional actual ZFR ordinal-monotonicity proofs for arbitrary Dn counts. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
  NumericalInstantiation SourceOrdinalPredicate SourceDomainInstances SourceRawSubset SourceRawSubsetBounds
  SourceHierarchySyntax SourceD0Recipe SourceD0ConditionalBase SourceFiniteCutoffShift SourceQuantifierRules
  SourceDn SourceDnBounds SourceDnConditionalMap SourceDnCutoffDiamonds SourceThreeConditions
  SourceDescriptorProvability SourceSetTheoryDescriptors SourceZFRProvability.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code.

Theorem source_zfr_dn_ordinal_monotonicity M domain level phi count d0 dn da db od oe subset law k l :
  source_bounded M domain(code_numeral M 1) ->source_bounded M phi(succM M k) ->
  source_bounded M d0(addM M count(succM M(succM M l))) ->
  source_LL_instance M(code_numeral M 1)(zeroM M)level ->source_d0_recipe M domain level phi d0 ->
  source_dn M count d0 dn ->source_formula_shift M dn da ->source_cutoff_shift M 1 dn db ->
  numerical_instantiation M(source_ordinal_predicate_code M)(code_numeral M 1)od ->
  numerical_instantiation M(source_ordinal_predicate_code M)(zeroM M)oe ->
  source_raw_subset_graph M(code_numeral M 1)(zeroM M)subset ->
  source_three_curried M od oe subset da db law ->source_zfr_provable M law.
Proof.
  intros HD HB HBD0 HL HD0 HDN HDA HDB HOD HOE HS HLaw.
  destruct(source_cutoff_shift_total M 0 d0) as(pa&HPA0).
  pose proof(proj2(source_formula_shift_cutoff_zero M d0 pa) HPA0) as HPA.
  destruct(source_cutoff_shift_total M 1 d0) as(pb&HPB).
  destruct(source_zfr_d0_conditional_base M domain level phi d0 pa pb od oe subset k
    HD HB HL HD0 HPA HPB HOD HOE HS) as(condition&baseMap&base&HC&HCond&HBaseMap&HBase&PBase).
  destruct(sf_relation_total M SFImpl da db) as(resultMap&HResultMap).
  destruct(sf_relation_total M SFImpl condition resultMap) as(result&HResult).
  pose proof(source_descriptor_dn_conditional_map M ZFRSourceDescriptor count condition d0 pa pb dn da db l
    baseMap base resultMap result HC HBD0 HDN HPA HPB HDA HDB HBaseMap HBase HResultMap HResult
    (proj2(source_zfr_descriptor_provable M base) PBase)) as PResult.
  pose proof(proj1(source_zfr_descriptor_provable M result) PResult) as PResultZFR.
  pose proof(source_dn_bounded M count d0 dn l HDN HBD0) as BDN.
  pose proof(source_cutoff_shift_bounded M 0 dn da(succM M(succM M l)) BDN
    (proj1(source_formula_shift_cutoff_zero M dn da) HDA)) as BDA.
  pose proof(source_cutoff_shift_bounded M 1 dn db(succM M l) BDN HDB) as BDB.
  assert(HNameD:coding_lt M(code_numeral M 1)(succM M(succM M(succM M l)))).
  { apply coding_lt_succ_cancel,coding_zero_lt_succ. }
  assert(HNameE:coding_lt M(zeroM M)(succM M(succM M(succM M l)))) by apply coding_zero_lt_succ.
  pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)(code_numeral M 1)od _
    (source_ordinal_predicate_bounded M) HNameD HOD) as BOD.
  pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)(zeroM M)oe _
    (source_ordinal_predicate_bounded M) HNameE HOE) as BOE.
  pose proof(source_raw_subset_bounded M(code_numeral M 1)(zeroM M)subset _ HNameD HNameE HS) as BS.
  exact(proj2(source_zfr_three_conditions_conversion M od oe subset da db condition result law _
    BOD BOE BS BDA BDB HCond HLaw(ex_intro _ resultMap(conj HResultMap HResult))) PResultZFR).
Qed.

Print Assumptions source_zfr_dn_ordinal_monotonicity.
