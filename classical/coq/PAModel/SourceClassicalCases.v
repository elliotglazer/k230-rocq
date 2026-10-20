(** Actual source case distinction from the calculus's Peirce axiom.
    No meta-level excluded-middle principle is used to choose a branch. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  NumericalContexts NumericalSourceFull SourcePropositionalTemplates SetSchemaConstructors.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Definition source_cases_positive :=SPTImpl (SPTSlot 0) (SPTSlot 1).
Definition source_cases_negative :=SPTImpl (SPTImpl (SPTSlot 0) SPTFalse) (SPTSlot 1).

Theorem source_classical_cases_program :source_prop_program
  [source_cases_positive;source_cases_negative] (SPTSlot 1).
Proof.
  eapply SPTIE;[exact (SPTPc _ (SPTSlot 1) SPTFalse)|].
  apply SPTII. eapply (SPTIE _ (SPTImpl (SPTSlot 0) SPTFalse) (SPTSlot 1)).
  - apply SPTCtx. now right;right;left.
  - apply SPTII. eapply SPTIE.
    + apply SPTCtx. now right;left.
    + eapply SPTIE.
      * apply SPTCtx. now right;right;left.
      * apply SPTCtx. now left.
Qed.

Theorem source_full_classical_cases M b c n test goal neg positive negative :
  sf_relation M SFImpl test (zeroM M) neg ->sf_relation M SFImpl test goal positive ->
  sf_relation M SFImpl neg goal negative ->source_full_prv M b c n positive ->
  source_full_prv M b c n negative ->source_full_prv M b c n goal.
Proof.
  intros HN HP HM PP PM.
  destruct (source_full_prv_wellformed M b c n positive PP) as (k&HBound&HCtx).
  destruct (proj1 (source_bounded_accept_binary M SFImpl test goal positive k
    (or_intror (or_intror eq_refl)) HP) HBound) as (HT&HG).
  assert (HB:forall i,source_bounded M (schema_env3 test goal (zeroM M) i) k).
  { intros [|[|i]];cbn [schema_env3];try assumption. apply source_bounded_accept_falsity. }
  assert (HPos:code_relation M (schema_env3 test goal (zeroM M))
    (source_prop_expression source_cases_positive) positive).
  { exact (source_prop_template_join M _ SFImpl (SPTSlot 0) (SPTSlot 1) test goal positive
      eq_refl eq_refl HP). }
  assert (HNeg:code_relation M (schema_env3 test goal (zeroM M))
    (source_prop_expression source_cases_negative) negative).
  { apply (source_prop_template_join M _ SFImpl (SPTImpl (SPTSlot 0) SPTFalse)
      (SPTSlot 1) neg goal negative);[|reflexivity|exact HM].
    exact (source_prop_template_join M _ SFImpl (SPTSlot 0) SPTFalse test (zeroM M) neg
      eq_refl eq_refl HN). }
  apply (source_prop_program_sound M _ _ source_classical_cases_program
    (schema_env3 test goal (zeroM M)) k b c n goal HB HCtx);[|reflexivity].
  intros a [<-|[<-|[]]] f HF.
  - pose proof (code_relation_functional M _ _ f positive HF HPos) as E. now subst f.
  - pose proof (code_relation_functional M _ _ f negative HF HNeg) as E. now subst f.
Qed.

Print Assumptions source_classical_cases_program.
Print Assumptions source_full_classical_cases.
