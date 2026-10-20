(** Actual CB successor proof assembly. Its single explicit mathematical
    input is the already proved canonical ordinal-monotonicity formula. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
  NumericalInstantiation SourceInstantiationConstructors SourceDomainInstances SourceHierarchySyntax SourceLFixed
  SourceOrdinalPredicate SourceQfRecipe SourceCBGoal SourceCBProofProperty SourceCBTotality SourceCBTotalityCollapse
  SourceCBMonotoneCollapse SourceCBGraphs SourceCBOutput SourceOrdinalCollectionActual SourceOrdinalInitialBounds
  SourceDescriptorClosure SourceDescriptorInstantiation SourceDescriptorProvability SourceSetTheoryDescriptors
  SourceZFRProvability SourcePropositionalTemplates SourceWitnessProofComposition SourceFunctionalityShells.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code source_L_domain_code.

Theorem source_cb_descriptor_instantiate M T f t g:
  source_descriptor_provable M T f ->numerical_instantiation M f t g ->source_descriptor_provable M T g.
Proof.
  intros HP HG. destruct(sf_relation_total M SFAll f(zeroM M)) as(all&HA).
  exact(source_descriptor_provable_all_elim M T f all t g
    (source_descriptor_provable_all M T f all HP HA)HA HG).
Qed.

Definition source_cb_four_environment {A}(o t m g:A)i:=match i with 0=>o|1=>t|2=>m|_=>g end.
Definition source_cb_oc_imp_template:=SPTImpl(SPTSlot 1)(SPTImpl(SPTSlot 2)(SPTSlot 3)).
Definition source_cb_total_goal_template:=SPTImpl(SPTSlot 1)(SPTSlot 3).
Definition source_cb_ord_total_template:=SPTImpl(SPTSlot 0)(SPTSlot 1).
Definition source_cb_ord_goal_template:=SPTImpl(SPTSlot 0)(SPTSlot 3).

Lemma source_cb_use_mono_program:source_prop_program
  [source_cb_oc_imp_template;SPTSlot 2]source_cb_total_goal_template.
Proof.
  unfold source_cb_oc_imp_template,source_cb_total_goal_template.
  apply SPTII. eapply SPTIE.
  - eapply SPTIE.
    + apply SPTCtx. right;now left.
    + apply SPTCtx. now left.
  - apply SPTCtx. right;right;now left.
Qed.

Lemma source_cb_compose_total_program:source_prop_program
  [source_cb_ord_total_template;source_cb_total_goal_template]source_cb_ord_goal_template.
Proof.
  unfold source_cb_ord_total_template,source_cb_total_goal_template,source_cb_ord_goal_template.
  apply SPTII. eapply SPTIE.
  - apply SPTCtx. right;right;now left.
  - eapply SPTIE.
    + apply SPTCtx. right;now left.
    + apply SPTCtx. now left.
Qed.

Theorem source_cb_successor_use M level count phi q mono g ordinal goal implication n:
  source_LL_instance M(code_numeral M 1)(zeroM M)level ->
  source_cb_proof_at M(source_L_domain_code M)level(source_ordinal_predicate_code M)count ->
  source_bounded M phi(addM M count(succM M(succM M n))) ->
  source_qf_recipe M(source_L_domain_code M)level count phi q ->
  source_cb_monotonicity_graph M q mono ->source_zfr_provable M mono ->
  coding_lt M g(succM M n) ->numerical_instantiation M(source_ordinal_predicate_code M)g ordinal ->
  source_cb_goal M(source_L_domain_code M)level(source_ordinal_predicate_code M)(succM M count)phi goal ->
  sf_relation M SFImpl ordinal goal implication ->source_zfr_provable M implication.
Proof.
  intros HL IH HB HQ HMono PMono HG HOrdinal HGoal HImp.
  pose proof(source_LL_instance_bounded M(code_numeral M 1)(zeroM M)level(code_numeral M 2)
    (coding_lt_succ M(code_numeral M 1))(coding_zero_lt_succ M(code_numeral M 1))HL) as HLevelB.
  pose proof(source_qf_recipe_bounded M(source_L_domain_code M)level count phi q n
    (numerical_L_domain_bounded M)HLevelB HB HQ) as HQB.
  destruct(source_zfr_ordinal_collection_theorem_total M q(succM M n)HQB)
    as(oldTotal&oldMono&oldOutput&oldTail&oldImp&HOT&HOM&HOO&HOTail&HOImp&POld).
  destruct(source_cb_totality_total M q) as(total&HTotal).
  pose proof(source_cb_oc_totality_instantiation M q oldTotal total(succM M(succM M(succM M n)))
    HQB HOT HTotal) as HITotal.
  destruct(numerical_instantiation_total M oldMono(zeroM M)) as(mono'&HIMono').
  pose proof(source_cb_initial_monotonicity_instance M q oldMono mono'(succM M(succM M(succM M n)))
    HQB HOM HIMono') as HMono'.
  pose proof(source_cb_monotonicity_functional M q mono' mono HMono' HMono) as E. subst mono'.
  pose proof(source_cb_oc_output_instantiation M(source_L_domain_code M)level count phi q oldOutput goal n
    (numerical_L_domain_bounded M)HLevelB HB HQ HOO HGoal) as HIOutput.
  destruct(sf_relation_total M SFImpl mono goal) as(tail&HTail).
  destruct(sf_relation_total M SFImpl total tail) as(instance&HInstance).
  pose proof(source_instantiation_binary M SFImpl oldMono oldOutput oldTail(zeroM M)mono goal tail
    (or_intror(or_intror eq_refl))HOTail HIMono' HIOutput HTail) as HITail.
  pose proof(source_instantiation_binary M SFImpl oldTotal oldTail oldImp(zeroM M)total tail instance
    (or_intror(or_intror eq_refl))HOImp HITotal HITail HInstance) as HIInstance.
  pose proof(source_cb_descriptor_instantiate M ZFRSourceDescriptor oldImp(zeroM M)instance
    (proj2(source_zfr_descriptor_provable M oldImp)POld)HIInstance) as PInstance.
  destruct(sf_relation_total M SFImpl ordinal total) as(ordTotal&HOrdTotal).
  pose proof(source_cb_ih_totality M level count phi q g ordinal total ordTotal n
    HL IH HB HG HQ HOrdinal HTotal HOrdTotal) as POrdTotal.
  assert(HGoalB:source_bounded M goal(succM M n)).
  { apply(source_cb_goal_bounded M(source_L_domain_code M)level(source_ordinal_predicate_code M)
      (succM M count)phi goal n(numerical_L_domain_bounded M)HLevelB(source_ordinal_predicate_bounded M));[|exact HGoal].
    rewrite Arithmetic.add_succ,<-qf_add_succ_right. exact HB. }
  pose proof(numerical_instantiation_bounded M oldTotal(zeroM M)total(succM M n)
    (source_oc_initial_totality_bounded M q oldTotal(succM M n)HQB HOT)(coding_zero_lt_succ M n)HITotal) as HTotalB.
  pose proof(numerical_instantiation_bounded M oldMono(zeroM M)mono(succM M n)
    (source_oc_initial_monotonicity_bounded M q oldMono(succM M n)HQB HOM)(coding_zero_lt_succ M n)HIMono') as HMonoB.
  pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)g ordinal(succM M n)
    (source_ordinal_predicate_bounded M)HG HOrdinal) as HOrdinalB.
  assert(HEnv:forall i,source_bounded M(source_cb_four_environment ordinal total mono goal i)(succM M n)).
  { intros[|[|[|i]]];cbn[source_cb_four_environment];assumption. }
  destruct(sf_relation_total M SFImpl total goal) as(totalGoal&HTG).
  assert(HInstanceGraph:code_relation M(source_cb_four_environment ordinal total mono goal)
    (source_prop_expression source_cb_oc_imp_template)instance).
  { unfold source_cb_oc_imp_template,source_prop_expression. functionality_graph. }
  assert(HTGGraph:code_relation M(source_cb_four_environment ordinal total mono goal)
    (source_prop_expression source_cb_total_goal_template)totalGoal).
  { unfold source_cb_total_goal_template,source_prop_expression. functionality_graph. }
  pose proof(source_zfr_prop_two M source_cb_oc_imp_template(SPTSlot 2)source_cb_total_goal_template
    source_cb_use_mono_program(source_cb_four_environment ordinal total mono goal)(succM M n)
    instance mono totalGoal HEnv HInstanceGraph eq_refl HTGGraph
    (proj1(source_zfr_descriptor_provable M instance)PInstance)PMono) as PTG.
  apply(source_zfr_prop_two M source_cb_ord_total_template source_cb_total_goal_template source_cb_ord_goal_template
    source_cb_compose_total_program(source_cb_four_environment ordinal total mono goal)(succM M n)
    ordTotal totalGoal implication HEnv);try assumption.
Qed.

Print Assumptions source_cb_descriptor_instantiate.
Print Assumptions source_cb_use_mono_program.
Print Assumptions source_cb_compose_total_program.
Print Assumptions source_cb_successor_use.
