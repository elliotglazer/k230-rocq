(** The positive ex_cond witness point: an ordinal x, its actual hierarchy
    carrier and a PCf-bound witness produce the literal existential goal. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
  NumericalInstantiation SourceDomainInstances SourceOrdinalPredicate SourceHierarchySyntax SourcePieceConjunction SourcePieceConjunctionBounds
  SourceReflectionCondition SourceReflectionConditionBounds SourceReflectionConditionPrograms SourceReflectionCarrierAll SourceReflectionConditionWitness
  SourceReflectionExistenceGoal SourceReflectionExistenceIntroduction SourcePieceBoundBody SourcePieceBoundTwoWitnesses
  SourceWitnessProofComposition SourcePropositionalTemplates SourceFunctionalityShells SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code.

Definition reflection_point_condition:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTImpl(SPTSlot 2)(SPTImpl(SPTSlot 3)(SPTSlot 4)))).
Definition reflection_point_intro:=SPTImpl(SPTAnd(SPTSlot 5)(SPTSlot 4))(SPTSlot 6).
Definition reflection_point_output:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTImpl(SPTAnd(SPTAnd(SPTSlot 5)(SPTSlot 2))(SPTSlot 3))(SPTSlot 6))).
Theorem source_reflection_existence_point_program:source_prop_program[reflection_point_condition;reflection_point_intro]reflection_point_output.
Proof.
  unfold reflection_point_condition,reflection_point_intro,reflection_point_output.
  apply SPTII,SPTII,SPTII. eapply SPTIE;[apply SPTCtx;right;right;right;right;now left|]. apply SPTCI.
  - eapply SPTCE1,SPTCE1. apply SPTCtx. now left.
  - eapply SPTIE.
    + eapply SPTIE.
      * eapply SPTIE.
        -- eapply SPTIE;apply SPTCtx;[right;right;right;now left|right;right;now left].
        -- apply SPTCtx. right;now left.
      * eapply SPTCE2,SPTCE1. apply SPTCtx. now left.
    + eapply SPTCE2. apply SPTCtx. now left.
Qed.

Theorem source_zfr_reflection_existence_point M domain level sb sc n x d X ordinal known body goal bodyGoal knownGoal law k:
  source_bounded M domain(code_numeral M 1) ->source_LL_instance M(code_numeral M 1)(zeroM M)level ->
  source_piece_table_valid M sb sc n ->coding_lt M x k ->coding_lt M d k ->coding_lt M X k ->
  numerical_instantiation M(source_ordinal_predicate_code M)x ordinal ->source_LL_instance M x X known ->
  source_pcf_bound_body M domain level sb sc n x X d body ->source_reflection_existence_goal M domain level sb sc n x goal ->
  sf_relation M SFImpl body goal bodyGoal ->sf_relation M SFImpl known bodyGoal knownGoal ->sf_relation M SFImpl ordinal knownGoal law ->
  source_zfr_provable M law.
Proof.
  intros HD HLevel HV HX HDk HXk HOrdinal HKnown(oldOrd&member&pc&left&HOldOrd&HMember&HPC&HLeft&HBody)HGoal HBodyGoal HKnownGoal HLaw.
  pose proof(source_LL_instance_bounded M(code_numeral M 1)(zeroM M)level(code_numeral M 2)
    (coding_lt_succ M(code_numeral M 1))(coding_zero_lt_succ M(code_numeral M 1))HLevel) as HL.
  destruct(source_reflection_condition_total M domain level(source_ordinal_predicate_code M)sb sc n x d) as(condition&HCondition).
  pose proof HCondition as HConditionSave.
  destruct HCondition as(ord'&member'&lev&newPc&point&all&both&HOrd'&HMember'&HLev&HNewPc&HPoint&HAll&HBoth&HCond).
  pose proof(numerical_instantiation_functional M(source_ordinal_predicate_code M)x ord' ordinal HOrd' HOrdinal) as E. subst ord'.
  pose proof(sf_relation_functional M SFMember x d member' member HMember' HMember) as E. subst member'.
  destruct(sf_relation_total M SFImpl pc condition) as(t1&HT1).
  destruct(sf_relation_total M SFImpl member t1) as(t2&HT2).
  destruct(sf_relation_total M SFImpl known t2) as(t3&HT3).
  destruct(sf_relation_total M SFImpl ordinal t3) as(conditionLaw&HConditionLaw).
  assert(PCondition:source_zfr_provable M conditionLaw).
  { apply(source_zfr_reflection_condition_witness M domain level sb sc n x d X ordinal known member pc condition conditionLaw k
      HD HLevel HV HX HDk HXk HOrdinal HKnown HMember HPC HConditionSave).
    exists all. split.
    - unfold source_reflection_condition_output,source_prop_expression. functionality_graph.
    - exists lev,newPc,point,both. auto 10. }
  destruct(sf_relation_total M SFAnd oldOrd condition) as(instance&HInstance).
  destruct(sf_relation_total M SFImpl instance goal) as(intro&HIntro).
  pose proof(source_zfr_reflection_existence_introduction M domain level sb sc n x d oldOrd condition instance goal intro k
    HD HL HV HX HDk HOldOrd HConditionSave HInstance HGoal HIntro) as PIntro.
  pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)x ordinal k(source_ordinal_predicate_bounded M)HX HOrdinal) as BO.
  pose proof(source_LL_instance_bounded M x X known k HX HXk HKnown) as BK.
  pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)d oldOrd k(source_ordinal_predicate_bounded M)HDk HOldOrd) as BDO.
  pose proof(proj2(source_bounded_accept_atom M SFMember x d member k(or_introl eq_refl)HMember)(conj HX HDk)) as BM.
  pose proof(source_piece_conjunction_bounded M n domain level sb sc d X pc k HD HL HV HDk HXk HPC) as BP.
  pose proof(source_reflection_condition_bounded M domain level(source_ordinal_predicate_code M)sb sc n x d condition k
    HD HL(source_ordinal_predicate_bounded M)HV HX HDk HConditionSave) as BC.
  pose proof(source_reflection_existence_bounded M domain level sb sc n x goal k HD HL HV HX HGoal) as BG.
  apply(source_zfr_prop_two M reflection_point_condition reflection_point_intro reflection_point_output source_reflection_existence_point_program
    (source_pcf_seven_environment ordinal known member pc condition oldOrd goal)k conditionLaw intro law).
  - intros[|[|[|[|[|[|i]]]]]];cbn[source_pcf_seven_environment];assumption.
  - unfold reflection_point_condition,source_prop_expression. functionality_graph.
  - unfold reflection_point_intro,source_prop_expression. functionality_graph.
  - unfold reflection_point_output,source_prop_expression. functionality_graph.
  - exact PCondition.
  - exact PIntro.
Qed.

Print Assumptions source_reflection_existence_point_program.
Print Assumptions source_zfr_reflection_existence_point.
