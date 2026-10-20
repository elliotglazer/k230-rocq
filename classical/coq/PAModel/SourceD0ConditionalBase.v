(** Actual conditional base for ordinal monotonicity of arbitrary Dn counts. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded SourceBoundMonotone
  NumericalInstantiation SourceFiniteCutoffShift SourceQuantifierRules SourceHierarchySyntax SourceD0At SourceD0Recipe
  SourceD0OrdinalInsertions SourceD0MonotonicityZFR SourceOrdinalPredicate SourceDomainInstances
  SourceRawSubset SourceRawSubsetBounds SourceThreeConditions SourceZFRProvability.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code.

Theorem source_zfr_d0_conditional_base M domain level phi d0 da db od oe subset k :
  source_bounded M domain(code_numeral M 1) ->source_bounded M phi(succM M k) ->
  source_LL_instance M(code_numeral M 1)(zeroM M)level ->source_d0_recipe M domain level phi d0 ->
  source_formula_shift M d0 da ->source_cutoff_shift M 1 d0 db ->
  numerical_instantiation M(source_ordinal_predicate_code M)(code_numeral M 1)od ->
  numerical_instantiation M(source_ordinal_predicate_code M)(zeroM M)oe ->
  source_raw_subset_graph M(code_numeral M 1)(zeroM M)subset ->
  exists condition baseMap base,
    source_bounded M condition(code_numeral M 2) /\source_three_conditions M od oe subset condition /\
    sf_relation M SFImpl da db baseMap /\sf_relation M SFImpl condition baseMap base /\source_zfr_provable M base.
Proof.
  intros HD HB HL HG HDA HDB HOD HOE HS.
  destruct(source_cutoff_shift_total M 1 phi) as(p1&H1).
  destruct(source_cutoff_shift_total M 1 p1) as(p2&H2).
  destruct(source_cutoff_shift_total M 1 p2) as(p3&H3).
  destruct(source_d0_recipe_ordinal_insertions M domain level phi p1 p2 p3 d0 da db k HD HB HL H1 H2 H3 HG HDA HDB) as[HAtD HAtE].
  pose proof(source_cutoff_shift_thrice_bounded M phi p3 k HB(ex_intro _ p1(ex_intro _ p2(conj H1(conj H2 H3))))) as BP3.
  assert(HNameD:coding_lt M(code_numeral M 1)(succM M(succM M(succM M k)))).
  { apply coding_lt_succ_cancel,coding_zero_lt_succ. }
  assert(HNameE:coding_lt M(zeroM M)(succM M(succM M(succM M k)))) by apply coding_zero_lt_succ.
  destruct(sf_relation_total M SFImpl da db) as(baseMap&HMap).
  destruct(sf_relation_total M SFImpl subset baseMap) as(t2&HT2).
  destruct(sf_relation_total M SFImpl oe t2) as(t1&HT1).
  destruct(sf_relation_total M SFImpl od t1) as(law&HLaw).
  pose proof(source_zfr_d0_monotonicity M domain p3(code_numeral M 1)(zeroM M)
    od oe subset da db baseMap t2 t1 law(succM M(succM M(succM M k)))
    HD BP3 HNameD HNameE HOD HOE HS HAtD HAtE HMap HT2 HT1 HLaw) as PLaw.
  destruct(sf_relation_total M SFAnd oe subset) as(bc&HBC).
  destruct(sf_relation_total M SFAnd od bc) as(condition&HCond).
  destruct(sf_relation_total M SFImpl condition baseMap) as(base&HBase).
  assert(BOD2:source_bounded M od(code_numeral M 2)).
  { exact(source_domain_instance_bound M(source_ordinal_predicate_code M)(code_numeral M 1)od(code_numeral M 2)
      (source_ordinal_predicate_bounded M)(coding_lt_succ M(code_numeral M 1)) HOD). }
  assert(BOE2:source_bounded M oe(code_numeral M 2)).
  { exact(source_domain_instance_bound M(source_ordinal_predicate_code M)(zeroM M)oe(code_numeral M 2)
      (source_ordinal_predicate_bounded M)(coding_zero_lt_succ M(code_numeral M 1)) HOE). }
  assert(BS2:source_bounded M subset(code_numeral M 2)).
  { exact(source_raw_subset_bounded M(code_numeral M 1)(zeroM M)subset(code_numeral M 2)
      (coding_lt_succ M(code_numeral M 1))(coding_zero_lt_succ M(code_numeral M 1)) HS). }
  assert(BC2:source_bounded M condition(code_numeral M 2)).
  { apply(proj2(source_bounded_accept_binary M SFAnd od bc condition _ (or_introl eq_refl) HCond)). split;[exact BOD2|].
    exact(proj2(source_bounded_accept_binary M SFAnd oe subset bc _ (or_introl eq_refl) HBC)(conj BOE2 BS2)). }
  assert(BOD:source_bounded M od(succM M(succM M(succM M k)))).
  { exact(source_domain_instance_bound M(source_ordinal_predicate_code M)(code_numeral M 1)od _
      (source_ordinal_predicate_bounded M) HNameD HOD). }
  assert(BOE:source_bounded M oe(succM M(succM M(succM M k)))).
  { exact(source_domain_instance_bound M(source_ordinal_predicate_code M)(zeroM M)oe _
      (source_ordinal_predicate_bounded M) HNameE HOE). }
  pose proof(source_raw_subset_bounded M(code_numeral M 1)(zeroM M)subset _ HNameD HNameE HS) as BS.
  pose proof(source_d0_at_bounded M domain p3(code_numeral M 1)da _ HD BP3 HNameD HAtD) as BDA.
  pose proof(source_d0_at_bounded M domain p3(zeroM M)db _ HD BP3 HNameE HAtE) as BDB.
  assert(HC:source_three_conditions M od oe subset condition) by(exists bc;auto).
  assert(HL3:source_three_curried M od oe subset da db law) by(exists baseMap,t2,t1;auto).
  assert(HG3:exists de,sf_relation M SFImpl da db de /\sf_relation M SFImpl condition de base) by(exists baseMap;auto).
  exists condition,baseMap,base. split;[exact BC2|]. split;[exact HC|]. split;[exact HMap|]. split;[exact HBase|].
  exact(proj1(source_zfr_three_conditions_conversion M od oe subset da db condition base law _
    BOD BOE BS BDA BDB HC HL3 HG3) PLaw).
Qed.

Print Assumptions source_zfr_d0_conditional_base.
