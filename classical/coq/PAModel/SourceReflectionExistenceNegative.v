(** The nonordinal branch of ex_cond. An actual fixed ordinal-existence
    proof supplies the witness; Cond follows by ordinary source falsity
    elimination from the displayed nonordinal assumption. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
  NumericalInstantiation NumericalRenaming NumericalContextRenaming SourceDomainInstances SourceOrdinalPredicate
  SourceHierarchySyntax SourcePieceConjunctionBounds SourceReflectionCondition SourceReflectionConditionBounds
  SourceReflectionExistenceGoal SourceReflectionExistenceIntroduction SourcePieceBoundTwoWitnesses
  SourceOrdinalExistsFixed SourceWitnessProofComposition SourcePropositionalTemplates SourceFunctionalityShells
  SourceDescriptorClosure SourceDescriptorProvability SourceSetTheoryDescriptors SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code source_ordinal_exists_code.

Definition source_reflection_negative_input:=SPTImpl(SPTAnd(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 2)))(SPTSlot 3).
Definition source_reflection_negative_output:=SPTImpl(SPTSlot 0)(SPTImpl(SPTImpl(SPTSlot 1)SPTFalse)(SPTSlot 3)).
Theorem source_reflection_negative_program :source_prop_program[source_reflection_negative_input]source_reflection_negative_output.
Proof.
  unfold source_reflection_negative_input,source_reflection_negative_output.
  apply SPTII,SPTII. eapply SPTIE;[apply SPTCtx;right;right;now left|]. apply SPTCI.
  - apply SPTCtx. right;now left.
  - apply SPTII,SPTExp. eapply SPTIE;apply SPTCtx;[right;now left|now left].
Qed.

Theorem source_zfr_reflection_existence_negative M domain level sb sc n x ordinal neg goal result k:
  source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->
  source_piece_table_valid M sb sc n ->coding_lt M x k ->
  numerical_instantiation M(source_ordinal_predicate_code M)x ordinal ->sf_relation M SFImpl ordinal(zeroM M)neg ->
  source_reflection_existence_goal M domain level sb sc n x goal ->sf_relation M SFImpl neg goal result ->
  source_zfr_provable M result.
Proof.
  intros HD HL HV HX HOrd HNeg HGoal HResult.
  pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)x ordinal k(source_ordinal_predicate_bounded M)HX HOrd) as BO.
  pose proof(proj2(source_bounded_accept_binary M SFImpl ordinal(zeroM M)neg k(or_intror(or_intror eq_refl))HNeg)
    (conj BO(source_bounded_accept_falsity M k))) as BN.
  pose proof(source_reflection_existence_bounded M domain level sb sc n x goal k HD HL HV HX HGoal) as BG.
  pose proof(proj2(source_bounded_accept_binary M SFImpl neg goal result k(or_intror(or_intror eq_refl))HResult)(conj BN BG)) as BR.
  destruct(numerical_renaming_total M ordinal(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)) as(ordinal'&HSOrd).
  pose proof(source_domain_instance_shift M(source_ordinal_predicate_code M)x ordinal ordinal'(source_ordinal_predicate_bounded M)HOrd HSOrd) as HOrd'.
  destruct(numerical_renaming_total M goal(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)) as(goal'&HSGoal).
  pose proof(source_reflection_existence_renaming M domain level sb sc n x goal(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)
    (succM M x)goal' HD HL HV HGoal HSGoal(proj2(context_shift_lookup M x(succM M x))eq_refl)) as HGoal'.
  destruct(source_reflection_condition_total M domain level(source_ordinal_predicate_code M)sb sc n(succM M x)(zeroM M)) as(condition&HCondition).
  pose proof HCondition as HCSave.
  destruct HCondition as(oldOrd&member&lev&pc&point&all&both&HOldOrd&HM&HLev&HPC&HP&HA&HB&HC).
  pose proof(numerical_instantiation_functional M(source_ordinal_predicate_code M)(succM M x)oldOrd ordinal' HOldOrd HOrd') as E. subst oldOrd.
  destruct(sf_relation_total M SFAnd(source_ordinal_predicate_code M)condition) as(body&HBody).
  destruct(sf_relation_total M SFImpl body goal') as(intro&HIntro).
  pose proof(source_zfr_reflection_existence_introduction M domain level sb sc n(succM M x)(zeroM M)
    (source_ordinal_predicate_code M)condition body goal' intro(succM M k)HD HL HV
    (proj2(coding_lt_succ_cancel M x k)HX)(coding_zero_lt_succ M k)
    (source_domain_instance_zero M(source_ordinal_predicate_code M)(source_ordinal_predicate_bounded M))HCSave HBody HGoal' HIntro) as PIntro.
  destruct(sf_relation_total M SFImpl ordinal'(zeroM M)) as(neg'&HNeg').
  destruct(sf_relation_total M SFImpl neg' goal') as(result'&HResult').
  destruct(sf_relation_total M SFImpl(source_ordinal_predicate_code M)result') as(witnessImp&HWitness).
  pose proof(source_reflection_condition_bounded M domain level(source_ordinal_predicate_code M)sb sc n(succM M x)(zeroM M)condition(succM M k)
    HD HL(source_ordinal_predicate_bounded M)HV(proj2(coding_lt_succ_cancel M x k)HX)(coding_zero_lt_succ M k)HCSave) as BC.
  destruct(proj1(source_bounded_accept_binary M SFImpl ordinal' both condition(succM M k)(or_intror(or_intror eq_refl))HC)BC) as[BO' BB].
  pose proof(source_reflection_existence_bounded M domain level sb sc n(succM M x)goal'(succM M k)
    HD HL HV(proj2(coding_lt_succ_cancel M x k)HX)HGoal') as BG'.
  assert(PWitness:source_zfr_provable M witnessImp).
  { apply(source_zfr_prop_one M source_reflection_negative_input source_reflection_negative_output source_reflection_negative_program
      (source_pcf_four_environment(source_ordinal_predicate_code M)ordinal' both goal')(succM M k)intro witnessImp).
    - intros[|[|[|i]]];cbn[source_pcf_four_environment];try assumption.
      exact(SourceRelativizationBounds.sr_domain_bound_succ M(source_ordinal_predicate_code M)k(source_ordinal_predicate_bounded M)).
    - unfold source_reflection_negative_input,source_prop_expression. functionality_graph.
    - unfold source_reflection_negative_output,source_prop_expression. functionality_graph.
    - exact PIntro. }
  assert(HSZero:SourceQuantifierRules.source_formula_shift M(zeroM M)(zeroM M)).
  { apply(proj2(numerical_renaming_invalid M(zeroM M)(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)(zeroM M)(or_introl eq_refl))). reflexivity. }
  pose proof(source_implication_shift_graph M ordinal(zeroM M)neg ordinal'(zeroM M)neg' HNeg HNeg' HSOrd HSZero) as HSNeg.
  pose proof(source_implication_shift_graph M neg goal result neg' goal' result' HResult HResult' HSNeg HSGoal) as HSResult.
  destruct(sf_relation_total M SFImpl(source_ordinal_exists_code M)result) as(use&HUse).
  pose proof(proj2(source_bounded_accept_unary M SFEx(source_ordinal_predicate_code M)(source_ordinal_exists_code M)(zeroM M)
    (or_intror eq_refl)(source_ordinal_exists_graph M))(source_ordinal_predicate_bounded M)) as BEx.
  pose proof(source_zfr_exists_implication M(source_ordinal_predicate_code M)(source_ordinal_exists_code M)result result' witnessImp use
    (zeroM M)k BEx BR(source_ordinal_exists_graph M)HSResult HWitness HUse PWitness) as PUse.
  apply(proj1(source_zfr_descriptor_provable M result)).
  exact(source_descriptor_provable_mp M ZFRSourceDescriptor(source_ordinal_exists_code M)result use
    (proj2(source_zfr_descriptor_provable M _)(source_zfr_ordinal_exists M))
    (proj2(source_zfr_descriptor_provable M use)PUse)HUse).
Qed.

Print Assumptions source_reflection_negative_program.
Print Assumptions source_zfr_reflection_existence_negative.
