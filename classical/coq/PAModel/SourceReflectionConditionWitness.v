(** An actual hierarchy witness and PCf bound yield the exact Cond clause. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded NumericalInstantiation
  SourceDomainInstances SourceOrdinalPredicate SourceHierarchySyntax SourcePieceConjunction SourcePieceConjunctionBounds
  SourceReflectionCondition SourceReflectionConditionBounds SourceReflectionConditionPrograms SourceReflectionCarrierAll
  SourceWitnessProofComposition SourcePropositionalTemplates SourceFunctionalityShells SourceZFRProvability.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code.

Theorem source_zfr_reflection_condition_witness M domain level sb sc n x d X ordinal known member pc condition law k:
  source_bounded M domain(code_numeral M 1) ->source_LL_instance M(code_numeral M 1)(zeroM M)level ->
  source_piece_table_valid M sb sc n ->coding_lt M x k ->coding_lt M d k ->coding_lt M X k ->
  numerical_instantiation M(source_ordinal_predicate_code M)x ordinal ->source_LL_instance M x X known ->
  sf_relation M SFMember x d member ->source_piece_conjunction M domain level sb sc n d X pc ->
  source_reflection_condition M domain level(source_ordinal_predicate_code M)sb sc n x d condition ->
  (exists all,code_relation M(source_reflection_six_environment ordinal known pc member all all)
    (source_prop_expression source_reflection_condition_output)law /\
    exists lev newPc point both,source_LL_instance M(succM M x)(zeroM M)lev /\
      source_piece_conjunction M domain level sb sc n(succM M d)(zeroM M)newPc /\sf_relation M SFImpl lev newPc point /\
      sf_relation M SFAll point(zeroM M)all /\sf_relation M SFAnd member all both /\sf_relation M SFImpl ordinal both condition) ->
  source_zfr_provable M law.
Proof.
  intros HD HLevel HV HX HDk HXk HOrd HKnown HMember HPC HCondition
    (all&HGraph&lev&newPc&point&both&HLev&HNewPc&HPoint&HAll&HBoth&HCond).
  pose proof(source_LL_instance_bounded M(code_numeral M 1)(zeroM M)level(code_numeral M 2)
    (coding_lt_succ M(code_numeral M 1))(coding_zero_lt_succ M(code_numeral M 1))HLevel) as HL.
  destruct(sf_relation_total M SFAnd ordinal known) as(left&HLeft).
  destruct(sf_relation_total M SFAnd left pc) as(joint&HJoint).
  destruct(sf_relation_total M SFImpl joint all) as(allLaw&HAllLaw).
  pose proof(source_zfr_reflection_carrier_all M domain level sb sc n x d X ordinal known pc left joint lev newPc point all allLaw k
    HD HLevel HV HX HDk HXk HOrd HKnown HPC HLeft HJoint HLev HNewPc HPoint HAll HAllLaw) as PAllLaw.
  pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)x ordinal k(source_ordinal_predicate_bounded M)HX HOrd) as BO.
  pose proof(source_LL_instance_bounded M x X known k HX HXk HKnown) as BK.
  pose proof(source_piece_conjunction_bounded M n domain level sb sc d X pc k HD HL HV HDk HXk HPC) as BP.
  pose proof(proj2(source_bounded_accept_atom M SFMember x d member k(or_introl eq_refl)HMember)(conj HX HDk)) as BM.
  pose proof(source_reflection_condition_bounded M domain level(source_ordinal_predicate_code M)sb sc n x d condition k
    HD HL(source_ordinal_predicate_bounded M)HV HX HDk HCondition) as BC.
  destruct(proj1(source_bounded_accept_binary M SFImpl ordinal both condition k(or_intror(or_intror eq_refl))HCond)BC) as[_ BB].
  destruct(proj1(source_bounded_accept_binary M SFAnd member all both k(or_introl eq_refl)HBoth)BB) as[_ BA].
  apply(source_zfr_prop_one M source_reflection_all_input source_reflection_condition_output source_reflection_condition_program
    (source_reflection_six_environment ordinal known pc member all all)k allLaw law).
  - intros[|[|[|[|[|i]]]]];cbn[source_reflection_six_environment];assumption.
  - unfold source_reflection_all_input,source_reflection_joint,source_prop_expression. functionality_graph.
  - exact HGraph.
  - exact PAllLaw.
Qed.

Print Assumptions source_zfr_reflection_condition_witness.
