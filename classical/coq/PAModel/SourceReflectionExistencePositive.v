(** Both positive ex_cond existential eliminations are actual source
    derivations: first the PCf bound, then a hierarchy carrier at x. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
  NumericalInstantiation NumericalRenaming SourceDomainInstances SourceOrdinalPredicate SourceLFixed SourceHierarchySyntax SourceHierarchyShifts SourceHierarchyExistsShell
  SourcePieceConjunctionBounds SourcePieceBoundGoal SourcePieceBoundBody SourcePieceBoundBodyBounds SourcePieceBoundUniform
  SourcePieceBoundOneWitness SourcePieceBoundTwoWitnesses SourceReflectionExistenceGoal SourceReflectionExistencePoint
  SourceWitnessProofComposition SourcePropositionalTemplates SourceFunctionalityShells SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code source_L_domain_code.

Definition reflection_permute3_input:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTImpl(SPTSlot 2)(SPTSlot 3))).
Definition reflection_permute3_output:=SPTImpl(SPTSlot 2)(SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 3))).
Theorem source_reflection_permute3_program:source_prop_program[reflection_permute3_input]reflection_permute3_output.
Proof.
  unfold reflection_permute3_input,reflection_permute3_output. apply SPTII,SPTII,SPTII.
  eapply SPTIE.
  - eapply SPTIE.
    + eapply SPTIE;apply SPTCtx;[right;right;right;now left|right;now left].
    + apply SPTCtx. now left.
  - apply SPTCtx. right;right;now left.
Qed.
Definition reflection_conditional_bound:=SPTImpl(SPTSlot 0)(SPTSlot 1).
Definition reflection_conditional_use:=SPTImpl(SPTSlot 1)(SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 2)(SPTSlot 3))).
Definition reflection_conditional_result:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 2)(SPTSlot 3)).
Theorem source_reflection_conditional_compose_program:source_prop_program
  [reflection_conditional_bound;reflection_conditional_use]reflection_conditional_result.
Proof.
  unfold reflection_conditional_bound,reflection_conditional_use,reflection_conditional_result.
  apply SPTII,SPTII. eapply SPTIE.
  - eapply SPTIE.
    + eapply SPTIE.
      * apply SPTCtx. right;right;right;now left.
      * eapply SPTIE;apply SPTCtx;[right;right;now left|right;now left].
    + apply SPTCtx. right;now left.
  - apply SPTCtx. now left.
Qed.
Definition reflection_duplicate_use:=SPTImpl(SPTSlot 1)(SPTImpl(SPTSlot 0)(SPTSlot 2)).
Definition reflection_duplicate_result:=SPTImpl(SPTSlot 0)(SPTSlot 2).
Theorem source_reflection_duplicate_compose_program:source_prop_program
  [reflection_conditional_bound;reflection_duplicate_use]reflection_duplicate_result.
Proof.
  unfold reflection_conditional_bound,reflection_duplicate_use,reflection_duplicate_result.
  apply SPTII. eapply SPTIE.
  - eapply SPTIE.
    + apply SPTCtx. right;right;now left.
    + eapply SPTIE;apply SPTCtx;[right;now left|now left].
  - apply SPTCtx. now left.
Qed.

Theorem source_zfr_reflection_existence_with_level M level sb sc n x X ordinal known goal tail law k:
  source_LL_instance M(code_numeral M 1)(zeroM M)level ->source_piece_table_valid M sb sc n ->
  coding_lt M x k ->coding_lt M X k ->numerical_instantiation M(source_ordinal_predicate_code M)x ordinal ->
  source_LL_instance M x X known ->source_reflection_existence_goal M(source_L_domain_code M)level sb sc n x goal ->
  sf_relation M SFImpl known goal tail ->sf_relation M SFImpl ordinal tail law ->source_zfr_provable M law.
Proof.
  intros HLevel HV HX HXk HOrdinal HKnown HGoal HTail HLaw.
  pose proof(numerical_L_domain_bounded M) as HD.
  pose proof(source_LL_instance_bounded M(code_numeral M 1)(zeroM M)level(code_numeral M 2)
    (coding_lt_succ M(code_numeral M 1))(coding_zero_lt_succ M(code_numeral M 1))HLevel) as HL.
  destruct(source_pcf_bound_goal_total M(source_L_domain_code M)level sb sc n x X) as(bound&HBound).
  destruct(sf_relation_total M SFImpl ordinal bound) as(boundLaw&HBoundLaw).
  pose proof(source_zfr_pcf_bound_uniform M level sb sc n x X ordinal bound boundLaw k HLevel HV HX HXk HOrdinal HBound HBoundLaw) as PBound.
  destruct(proj1(source_pcf_bound_goal_body M(source_L_domain_code M)level sb sc n x X bound)HBound) as(body&HBody&HEx).
  destruct(numerical_instantiation_total M(source_ordinal_predicate_code M)(succM M x)) as(ordinal'&HOrdinal').
  pose proof(source_domain_shift_to M(source_ordinal_predicate_code M)x ordinal ordinal'(source_ordinal_predicate_bounded M)HOrdinal HOrdinal') as HSOrdinal.
  destruct(source_LL_instance_total M(succM M x)(succM M X)) as(known'&HKnown').
  pose proof(source_LL_shift_to M x X known known' HKnown HKnown') as HSKnown.
  destruct(numerical_renaming_total M goal(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)) as(goal'&HSGoal).
  pose proof(source_reflection_existence_renaming M(source_L_domain_code M)level sb sc n x goal(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)
    (succM M x)goal' HD HL HV HGoal HSGoal(proj2(NumericalContextRenaming.context_shift_lookup M x(succM M x))eq_refl)) as HGoal'.
  destruct(sf_relation_total M SFImpl body goal') as(bg&HBG).
  destruct(sf_relation_total M SFImpl known' bg) as(kg&HKG).
  destruct(sf_relation_total M SFImpl ordinal' kg) as(point&HPoint).
  pose proof(source_zfr_reflection_existence_point M(source_L_domain_code M)level sb sc n(succM M x)(zeroM M)(succM M X)
    ordinal' known' body goal' bg kg point(succM M k)HD HLevel HV(proj2(coding_lt_succ_cancel M x k)HX)(coding_zero_lt_succ M k)
    (proj2(coding_lt_succ_cancel M X k)HXk)HOrdinal' HKnown' HBody HGoal' HBG HKG HPoint) as PPoint.
  destruct(sf_relation_total M SFImpl known' goal') as(tail'&HTail').
  destruct(sf_relation_total M SFImpl ordinal' tail') as(law'&HLaw').
  destruct(sf_relation_total M SFImpl body law') as(witnessImp&HWitness).
  pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)(succM M x)ordinal'(succM M k)(source_ordinal_predicate_bounded M)
    (proj2(coding_lt_succ_cancel M x k)HX)HOrdinal') as BO'.
  pose proof(source_LL_instance_bounded M(succM M x)(succM M X)known'(succM M k)
    (proj2(coding_lt_succ_cancel M x k)HX)(proj2(coding_lt_succ_cancel M X k)HXk)HKnown') as BK'.
  pose proof(source_pcf_bound_body_bounded M(source_L_domain_code M)level sb sc n(succM M x)(succM M X)(zeroM M)body(succM M k)
    HD HL HV(proj2(coding_lt_succ_cancel M x k)HX)(proj2(coding_lt_succ_cancel M X k)HXk)(coding_zero_lt_succ M k)HBody) as BB.
  pose proof(source_reflection_existence_bounded M(source_L_domain_code M)level sb sc n(succM M x)goal'(succM M k)
    HD HL HV(proj2(coding_lt_succ_cancel M x k)HX)HGoal') as BG'.
  assert(PWitness:source_zfr_provable M witnessImp).
  { apply(source_zfr_prop_one M reflection_permute3_input reflection_permute3_output source_reflection_permute3_program
      (source_pcf_four_environment ordinal' known' body goal')(succM M k)point witnessImp).
    - intros[|[|[|i]]];cbn[source_pcf_four_environment];assumption.
    - unfold reflection_permute3_input,source_prop_expression. functionality_graph.
    - unfold reflection_permute3_output,source_prop_expression. functionality_graph.
    - exact PPoint. }
  pose proof(source_implication_shift_graph M known goal tail known' goal' tail' HTail HTail' HSKnown HSGoal) as HSTail.
  pose proof(source_implication_shift_graph M ordinal tail law ordinal' tail' law' HLaw HLaw' HSOrdinal HSTail) as HSLaw.
  pose proof(source_pcf_bound_goal_bounded M(source_L_domain_code M)level sb sc n x X bound k HD HL HV HX HXk HBound) as BBound.
  pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)x ordinal k(source_ordinal_predicate_bounded M)HX HOrdinal) as BO.
  pose proof(source_LL_instance_bounded M x X known k HX HXk HKnown) as BK.
  pose proof(source_reflection_existence_bounded M(source_L_domain_code M)level sb sc n x goal k HD HL HV HX HGoal) as BG.
  pose proof(proj2(source_bounded_accept_binary M SFImpl known goal tail k(or_intror(or_intror eq_refl))HTail)(conj BK BG)) as BT.
  pose proof(proj2(source_bounded_accept_binary M SFImpl ordinal tail law k(or_intror(or_intror eq_refl))HLaw)(conj BO BT)) as BLaw.
  destruct(sf_relation_total M SFImpl bound law) as(use&HUse).
  pose proof(source_zfr_exists_implication M body bound law law' witnessImp use k k BBound BLaw HEx HSLaw HWitness HUse PWitness) as PUse.
  apply(source_zfr_prop_two M reflection_conditional_bound reflection_conditional_use reflection_conditional_result source_reflection_conditional_compose_program
    (source_pcf_four_environment ordinal bound known goal)k boundLaw use law).
  - intros[|[|[|i]]];cbn[source_pcf_four_environment];assumption.
  - unfold reflection_conditional_bound,source_prop_expression. functionality_graph.
  - unfold reflection_conditional_use,source_prop_expression. functionality_graph.
  - unfold reflection_conditional_result,source_prop_expression. functionality_graph.
  - exact PBound.
  - exact PUse.
Qed.

Theorem source_zfr_reflection_existence_positive M level sb sc n x ordinal goal positive k:
  source_LL_instance M(code_numeral M 1)(zeroM M)level ->source_piece_table_valid M sb sc n ->coding_lt M x k ->
  numerical_instantiation M(source_ordinal_predicate_code M)x ordinal ->
  source_reflection_existence_goal M(source_L_domain_code M)level sb sc n x goal ->sf_relation M SFImpl ordinal goal positive ->
  source_zfr_provable M positive.
Proof.
  intros HLevel HV HX HOrdinal HGoal HPositive.
  pose proof(numerical_L_domain_bounded M) as HD.
  pose proof(source_LL_instance_bounded M(code_numeral M 1)(zeroM M)level(code_numeral M 2)
    (coding_lt_succ M(code_numeral M 1))(coding_zero_lt_succ M(code_numeral M 1))HLevel) as HL.
  destruct(source_zfr_hierarchy_exists_shell M x) as(oldOrd&known&ex&existLaw&HExist&PExist).
  destruct HExist as(HOldOrd&HKnown&HEx&HExistLaw).
  pose proof(numerical_instantiation_functional M(source_ordinal_predicate_code M)x oldOrd ordinal HOldOrd HOrdinal) as E. subst oldOrd.
  destruct(numerical_instantiation_total M(source_ordinal_predicate_code M)(succM M x)) as(ordinal'&HOrdinal').
  pose proof(source_domain_shift_to M(source_ordinal_predicate_code M)x ordinal ordinal'(source_ordinal_predicate_bounded M)HOrdinal HOrdinal') as HSOrdinal.
  destruct(numerical_renaming_total M goal(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)) as(goal'&HSGoal).
  pose proof(source_reflection_existence_renaming M(source_L_domain_code M)level sb sc n x goal(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)
    (succM M x)goal' HD HL HV HGoal HSGoal(proj2(NumericalContextRenaming.context_shift_lookup M x(succM M x))eq_refl)) as HGoal'.
  destruct(sf_relation_total M SFImpl known goal') as(tail&HTail).
  destruct(sf_relation_total M SFImpl ordinal' tail) as(point&HPoint).
  pose proof(source_zfr_reflection_existence_with_level M level sb sc n(succM M x)(zeroM M)ordinal' known goal' tail point(succM M k)
    HLevel HV(proj2(coding_lt_succ_cancel M x k)HX)(coding_zero_lt_succ M k)HOrdinal' HKnown HGoal' HTail HPoint) as PPoint.
  destruct(sf_relation_total M SFImpl ordinal' goal') as(positive'&HPositive').
  destruct(sf_relation_total M SFImpl known positive') as(witnessImp&HWitness).
  pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)(succM M x)ordinal'(succM M k)(source_ordinal_predicate_bounded M)
    (proj2(coding_lt_succ_cancel M x k)HX)HOrdinal') as BO'.
  pose proof(source_LL_instance_bounded M(succM M x)(zeroM M)known(succM M k)(proj2(coding_lt_succ_cancel M x k)HX)(coding_zero_lt_succ M k)HKnown) as BK.
  pose proof(source_reflection_existence_bounded M(source_L_domain_code M)level sb sc n(succM M x)goal'(succM M k)
    HD HL HV(proj2(coding_lt_succ_cancel M x k)HX)HGoal') as BG'.
  assert(PWitness:source_zfr_provable M witnessImp).
  { apply(source_zfr_prop_one M(SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 2)))
      (SPTImpl(SPTSlot 1)(SPTImpl(SPTSlot 0)(SPTSlot 2)))source_pcf_exchange_program
      (source_pcf_four_environment ordinal' known goal' goal')(succM M k)point witnessImp).
    - intros[|[|[|i]]];cbn[source_pcf_four_environment];assumption.
    - unfold source_prop_expression. functionality_graph.
    - unfold source_prop_expression. functionality_graph.
    - exact PPoint. }
  pose proof(source_implication_shift_graph M ordinal goal positive ordinal' goal' positive' HPositive HPositive' HSOrdinal HSGoal) as HSPositive.
  pose proof(proj2(source_bounded_accept_unary M SFEx known ex k(or_intror eq_refl)HEx)BK) as BEx.
  pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)x ordinal k(source_ordinal_predicate_bounded M)HX HOrdinal) as BO.
  pose proof(source_reflection_existence_bounded M(source_L_domain_code M)level sb sc n x goal k HD HL HV HX HGoal) as BG.
  pose proof(proj2(source_bounded_accept_binary M SFImpl ordinal goal positive k(or_intror(or_intror eq_refl))HPositive)(conj BO BG)) as BP.
  destruct(sf_relation_total M SFImpl ex positive) as(use&HUse).
  pose proof(source_zfr_exists_implication M known ex positive positive' witnessImp use k k BEx BP HEx HSPositive HWitness HUse PWitness) as PUse.
  apply(source_zfr_prop_two M reflection_conditional_bound reflection_duplicate_use reflection_duplicate_result source_reflection_duplicate_compose_program
    (source_pcf_four_environment ordinal ex goal goal)k existLaw use positive).
  - intros[|[|[|i]]];cbn[source_pcf_four_environment];assumption.
  - unfold reflection_conditional_bound,source_prop_expression. functionality_graph.
  - unfold reflection_duplicate_use,source_prop_expression. functionality_graph.
  - unfold reflection_duplicate_result,source_prop_expression. functionality_graph.
  - exact PExist.
  - exact PUse.
Qed.

Print Assumptions source_reflection_permute3_program.
Print Assumptions source_reflection_conditional_compose_program.
Print Assumptions source_reflection_duplicate_compose_program.
Print Assumptions source_zfr_reflection_existence_with_level.
Print Assumptions source_zfr_reflection_existence_positive.
