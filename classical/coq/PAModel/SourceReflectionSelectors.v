(** The finite selector deductions in KUpperReflect.reflected_left/right.
    Actual class-reflection proofs are explicit inputs. These programs
    extract either chosen matrix component without analyzing its code. *)
From PAModel Require Import Model CodeExpressions SourceBounded NumericalContexts
  NumericalSourceFull SourcePropositionalTemplates.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Definition source_selector P A B :=SPTOr (SPTAnd P A) (SPTAnd (SPTImpl P SPTFalse) B).

Lemma source_reflected_left_program P A B C D :source_prop_program
  [P;SPTImpl (source_selector P A B) (source_selector P C D)] (SPTImpl A C).
Proof.
  apply SPTII.
  apply (SPTDE _ (SPTAnd P C) (SPTAnd (SPTImpl P SPTFalse) D) C).
  - apply (SPTIE _ (source_selector P A B) (source_selector P C D));[apply SPTCtx;cbn;tauto|].
    apply SPTDI1,SPTCI;apply SPTCtx;cbn;tauto.
  - apply (SPTCE2 _ P C),SPTCtx. now left.
  - apply SPTExp. apply (SPTIE _ P SPTFalse).
    + apply (SPTCE1 _ (SPTImpl P SPTFalse) D),SPTCtx. now left.
    + apply SPTCtx. cbn;tauto.
Qed.

Lemma source_reflected_right_program P A B C D :source_prop_program
  [SPTImpl P SPTFalse;SPTImpl (source_selector P A B) (source_selector P C D)] (SPTImpl B D).
Proof.
  apply SPTII.
  apply (SPTDE _ (SPTAnd P C) (SPTAnd (SPTImpl P SPTFalse) D) D).
  - apply (SPTIE _ (source_selector P A B) (source_selector P C D));[apply SPTCtx;cbn;tauto|].
    apply SPTDI2,SPTCI;apply SPTCtx;cbn;tauto.
  - apply SPTExp. apply (SPTIE _ P SPTFalse).
    + apply SPTCtx. cbn;tauto.
    + apply (SPTCE1 _ P C),SPTCtx. now left.
  - apply (SPTCE2 _ (SPTImpl P SPTFalse) D),SPTCtx. now left.
Qed.

Definition source_reflection_test (negative:bool) :=
  if negative then SPTImpl (SPTSlot 0) SPTFalse else SPTSlot 0.
Definition source_reflection_pair_left :=source_selector (SPTSlot 0) (SPTSlot 1) (SPTSlot 2).
Definition source_reflection_pair_right :=source_selector (SPTSlot 0) (SPTSlot 3) (SPTSlot 4).
Definition source_reflection_selected (negative:bool) :=
  if negative then SPTImpl (SPTSlot 2) (SPTSlot 4) else SPTImpl (SPTSlot 1) (SPTSlot 3).

Theorem source_full_reflection_selector M negative rho k b c n test reflection out :
  (forall i,source_bounded M (rho i) k) ->context_bounded M b c n k ->
  code_relation M rho (source_prop_expression (source_reflection_test negative)) test ->
  code_relation M rho (source_prop_expression
    (SPTImpl source_reflection_pair_left source_reflection_pair_right)) reflection ->
  code_relation M rho (source_prop_expression (source_reflection_selected negative)) out ->
  source_full_prv M b c n test ->source_full_prv M b c n reflection ->source_full_prv M b c n out.
Proof.
  intros HB HC HT HR HO PT PR.
  assert (HProgram:source_prop_program [source_reflection_test negative;
      SPTImpl source_reflection_pair_left source_reflection_pair_right]
      (source_reflection_selected negative)).
  { destruct negative;[apply source_reflected_right_program|apply source_reflected_left_program]. }
  apply (source_prop_program_sound M _ _ HProgram rho k b c n out HB HC);[|exact HO].
  intros a [<-|[<-|[]]] f HF.
  - rewrite (code_relation_functional M _ rho f test HF HT). exact PT.
  - rewrite (code_relation_functional M _ rho f reflection HF HR). exact PR.
Qed.

Print Assumptions source_reflected_left_program.
Print Assumptions source_reflected_right_program.
Print Assumptions source_full_reflection_selector.
