(** Fixed propositional programs used by the internal L_common induction. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  SourcePropositionalTemplates SourceFunctionalityShells SourceDescriptorPrograms SourceZFRProvability SourceSetTheoryDescriptors.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Definition source_common_ignore_program_template :=SPTImpl(SPTSlot 0)(SPTSlot 1).
Lemma source_common_ignore_program :source_prop_program[SPTSlot 1]source_common_ignore_program_template.
Proof. unfold source_common_ignore_program_template. apply SPTII,SPTCtx. cbn;tauto. Qed.
Definition source_common_step_previous :=SPTImpl(SPTSlot 0)(SPTSlot 2).
Definition source_common_step_successor :=SPTImpl(SPTSlot 2)(SPTImpl(SPTSlot 1)(SPTSlot 3)).
Definition source_common_step_conclusion :=SPTImpl(SPTAnd(SPTSlot 0)(SPTSlot 1))(SPTSlot 3).
Lemma source_common_step_program :source_prop_program[source_common_step_previous;source_common_step_successor]
  source_common_step_conclusion.
Proof.
  unfold source_common_step_previous,source_common_step_successor,source_common_step_conclusion.
  apply SPTII. eapply SPTIE with(a:=SPTSlot 1).
  - eapply SPTIE with(a:=SPTSlot 2).
    + apply SPTCtx. cbn;tauto.
    + eapply SPTIE with(a:=SPTSlot 0).
      * apply SPTCtx. cbn;tauto.
      * eapply SPTCE1. apply SPTCtx. cbn;tauto.
  - eapply SPTCE2. apply SPTCtx. cbn;tauto.
Qed.

Theorem source_zfr_common_ignore M block target out k :
  source_bounded M block k ->source_bounded M target k ->sf_relation M SFImpl block target out ->
  source_zfr_provable M target ->source_zfr_provable M out.
Proof.
  intros HB HT HG PT. apply(proj1(source_zfr_descriptor_provable M out)).
  set(rho:=fun j=>match j with 0=>block|_=>target end).
  apply(source_descriptor_prop_program M ZFRSourceDescriptor[SPTSlot 1]source_common_ignore_program_template
    source_common_ignore_program rho k out).
  - intros[|j];assumption.
  - intros p[<-|[]] g HE. change(g=target) in HE. subst g. exact(proj2(source_zfr_descriptor_provable M target)PT).
  - unfold source_common_ignore_program_template,source_prop_expression. functionality_graph.
Qed.

Theorem source_zfr_common_step M block ly old target previous tail successor last out k :
  source_bounded M block k ->source_bounded M ly k ->source_bounded M old k ->source_bounded M target k ->
  sf_relation M SFImpl block old previous ->sf_relation M SFImpl ly target tail ->
  sf_relation M SFImpl old tail successor ->sf_relation M SFAnd block ly last ->sf_relation M SFImpl last target out ->
  source_zfr_provable M previous ->source_zfr_provable M successor ->source_zfr_provable M out.
Proof.
  intros HB HLY HO HT HPrevious HTail HSuccessor HLast HOut PPrevious PSuccessor.
  set(rho:=fun j=>match j with 0=>block|1=>ly|2=>old|_=>target end).
  assert(HPrevGraph:code_relation M rho(source_prop_expression source_common_step_previous)previous).
  { unfold source_common_step_previous,source_prop_expression. functionality_graph. }
  assert(HSuccGraph:code_relation M rho(source_prop_expression source_common_step_successor)successor).
  { unfold source_common_step_successor,source_prop_expression. functionality_graph. }
  apply(proj1(source_zfr_descriptor_provable M out)).
  apply(source_descriptor_prop_program M ZFRSourceDescriptor
    [source_common_step_previous;source_common_step_successor]source_common_step_conclusion
    source_common_step_program rho k out).
  - intros[|[|[|j]]];assumption.
  - intros p[<-|[<-|[]]]g HE.
    + rewrite(code_relation_functional M _ rho g previous HE HPrevGraph). exact(proj2(source_zfr_descriptor_provable M previous)PPrevious).
    + rewrite(code_relation_functional M _ rho g successor HE HSuccGraph). exact(proj2(source_zfr_descriptor_provable M successor)PSuccessor).
  - unfold source_common_step_conclusion,source_prop_expression. functionality_graph.
Qed.
Print Assumptions source_zfr_common_ignore.
Print Assumptions source_zfr_common_step.
