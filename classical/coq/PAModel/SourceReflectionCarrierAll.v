(** Hierarchy uniqueness and actual PCf equality transport produce the
    universal carrier clause in Cond. All quantified matrices are internal. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
  NumericalRenaming NumericalInstantiation NumericalContextRenaming SourceDomainInstances SourceOrdinalPredicate
  SourceHierarchySyntax SourceHierarchyShifts SourceHierarchyWitnessShell SourcePieceConjunction SourcePieceConjunctionBounds
  SourcePieceConjunctionRenaming SourcePCfCarrierEquality SourceReflectionConditionPrograms SourceConditionalAllIntroduction
  SourceWitnessProofComposition SourcePropositionalTemplates SourceFunctionalityShells SourceZFRProvability.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code.

Definition source_reflection_six_environment {A:Type}(a b c d e f:A)(i:nat):=
  match i with 0=>a|1=>b|2=>c|3=>d|4=>e|_=>f end.

Theorem source_zfr_reflection_carrier_all M domain level sb sc n x d X ordinal known oldPc left joint
    lev newPc point all law k:
  source_bounded M domain(code_numeral M 1) ->source_LL_instance M(code_numeral M 1)(zeroM M)level ->
  source_piece_table_valid M sb sc n ->coding_lt M x k ->coding_lt M d k ->coding_lt M X k ->
  numerical_instantiation M(source_ordinal_predicate_code M)x ordinal ->source_LL_instance M x X known ->
  source_piece_conjunction M domain level sb sc n d X oldPc ->sf_relation M SFAnd ordinal known left ->sf_relation M SFAnd left oldPc joint ->
  source_LL_instance M(succM M x)(zeroM M)lev ->source_piece_conjunction M domain level sb sc n(succM M d)(zeroM M)newPc ->
  sf_relation M SFImpl lev newPc point ->sf_relation M SFAll point(zeroM M)all ->sf_relation M SFImpl joint all law ->
  source_zfr_provable M law.
Proof.
  intros HD HLevel HV HX HDk HXk HOrdinal HKnown HOldPc HLeft HJoint HLev HNewPc HPoint HAll HLaw.
  pose proof(source_LL_instance_bounded M(code_numeral M 1)(zeroM M)level(code_numeral M 2)
    (coding_lt_succ M(code_numeral M 1))(coding_zero_lt_succ M(code_numeral M 1))HLevel) as HL.
  pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)x ordinal k(source_ordinal_predicate_bounded M)HX HOrdinal) as BO.
  pose proof(source_LL_instance_bounded M x X known k HX HXk HKnown) as BK.
  pose proof(source_piece_conjunction_bounded M n domain level sb sc d X oldPc k HD HL HV HDk HXk HOldPc) as BP.
  pose proof(proj2(source_bounded_accept_binary M SFAnd ordinal known left k(or_introl eq_refl)HLeft)(conj BO BK)) as BL.
  pose proof(proj2(source_bounded_accept_binary M SFAnd left oldPc joint k(or_introl eq_refl)HJoint)(conj BL BP)) as BJ.
  destruct(numerical_instantiation_total M(source_ordinal_predicate_code M)(succM M x)) as(ordinal'&HOrdinal').
  pose proof(source_domain_shift_to M(source_ordinal_predicate_code M)x ordinal ordinal'(source_ordinal_predicate_bounded M)HOrdinal HOrdinal') as HSOrd.
  destruct(source_LL_instance_total M(succM M x)(succM M X)) as(known'&HKnown').
  pose proof(source_LL_shift_to M x X known known' HKnown HKnown') as HSKnown.
  destruct(numerical_renaming_total M oldPc(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)) as(oldPc'&HSPc).
  pose proof(source_piece_conjunction_renaming M n domain level sb sc d X oldPc(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)
    (succM M d)(succM M X)oldPc' HD HL HV HOldPc HSPc(proj2(context_shift_lookup M d(succM M d))eq_refl)
    (proj2(context_shift_lookup M X(succM M X))eq_refl)) as HOldPc'.
  destruct(sf_relation_total M SFAnd ordinal' known') as(left'&HLeft').
  destruct(sf_relation_total M SFAnd left' oldPc') as(joint'&HJoint').
  assert(HSLeft:SourceQuantifierRules.source_formula_shift M left left').
  { apply(proj2(numerical_renaming_binary M SFAnd ordinal known left(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)left'(or_introl eq_refl)HLeft)).
    exists ordinal',known'. auto. }
  assert(HSJoint:SourceQuantifierRules.source_formula_shift M joint joint').
  { apply(proj2(numerical_renaming_binary M SFAnd left oldPc joint(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)joint'(or_introl eq_refl)HJoint)).
    exists left',oldPc'. auto. }
  destruct(source_zfr_hierarchy_unique_shell M(succM M x)(succM M X)(zeroM M))
    as(oo&kk&ll&equal&t1&t2&unique&HUnique&PUnique).
  destruct HUnique as(HOO&HKK&HLL&HEq&HT2&HT1&HUnique).
  pose proof(numerical_instantiation_functional M(source_ordinal_predicate_code M)(succM M x)oo ordinal' HOO HOrdinal') as E. subst oo.
  pose proof(source_LL_instance_functional M(succM M x)(succM M X)kk known' HKK HKnown') as E. subst kk.
  pose proof(source_LL_instance_functional M(succM M x)(zeroM M)ll lev HLL HLev) as E. subst ll.
  destruct(sf_relation_total M SFImpl oldPc' newPc) as(map&HMap).
  destruct(sf_relation_total M SFImpl equal map) as(carrier&HCarrier).
  pose proof(source_zfr_pcf_carrier_equality_all M domain level HD HLevel n sb sc(succM M d)(succM M X)(zeroM M)
    equal oldPc' newPc map carrier(succM M k)HV(proj2(coding_lt_succ_cancel M d k)HDk)
    (proj2(coding_lt_succ_cancel M X k)HXk)(coding_zero_lt_succ M k)HEq HOldPc' HNewPc HMap HCarrier) as PCarrier.
  destruct(sf_relation_total M SFImpl joint' point) as(pointLaw&HPointLaw).
  pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)(succM M x)ordinal'(succM M k)(source_ordinal_predicate_bounded M)
    (proj2(coding_lt_succ_cancel M x k)HX)HOrdinal') as BO'.
  pose proof(source_LL_instance_bounded M(succM M x)(succM M X)known'(succM M k)
    (proj2(coding_lt_succ_cancel M x k)HX)(proj2(coding_lt_succ_cancel M X k)HXk)HKnown') as BK'.
  pose proof(source_LL_instance_bounded M(succM M x)(zeroM M)lev(succM M k)
    (proj2(coding_lt_succ_cancel M x k)HX)(coding_zero_lt_succ M k)HLev) as BLev.
  pose proof(source_piece_conjunction_bounded M n domain level sb sc(succM M d)(succM M X)oldPc'(succM M k)
    HD HL HV(proj2(coding_lt_succ_cancel M d k)HDk)(proj2(coding_lt_succ_cancel M X k)HXk)HOldPc') as BP'.
  pose proof(source_piece_conjunction_bounded M n domain level sb sc(succM M d)(zeroM M)newPc(succM M k)
    HD HL HV(proj2(coding_lt_succ_cancel M d k)HDk)(coding_zero_lt_succ M k)HNewPc) as BN.
  pose proof(proj2(source_bounded_accept_atom M SFEqual(succM M X)(zeroM M)equal(succM M k)(or_intror eq_refl)HEq)
    (conj(proj2(coding_lt_succ_cancel M X k)HXk)(coding_zero_lt_succ M k))) as BEq.
  assert(PPoint:source_zfr_provable M pointLaw).
  { apply(source_zfr_prop_two M source_reflection_unique_template source_reflection_carrier_template source_reflection_point_template
      source_reflection_point_program(source_reflection_six_environment ordinal' known' oldPc' lev equal newPc)(succM M k)unique carrier pointLaw).
    - intros[|[|[|[|[|i]]]]];cbn[source_reflection_six_environment];assumption.
    - unfold source_reflection_unique_template,source_prop_expression. functionality_graph.
    - unfold source_reflection_carrier_template,source_prop_expression. functionality_graph.
    - unfold source_reflection_point_template,source_reflection_joint,source_prop_expression. functionality_graph.
    - exact PUnique.
    - exact PCarrier. }
  pose proof(proj2(source_bounded_accept_binary M SFImpl lev newPc point(succM M k)(or_intror(or_intror eq_refl))HPoint)(conj BLev BN)) as BPoint.
  exact(source_zfr_conditional_all_introduction M joint joint' point all pointLaw law k BJ BPoint HSJoint HAll HPointLaw HLaw PPoint).
Qed.

Print Assumptions source_zfr_reflection_carrier_all.
