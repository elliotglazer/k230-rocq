(** Literal same-witness reordering for a guarded Replacement matrix. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  NumericalContexts NumericalSourceFull SourcePropositionalTemplates.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Definition wf_rep_raw_body := SPTAnd (SPTSlot 2) (SPTAnd (SPTAnd (SPTSlot 0) (SPTSlot 1)) (SPTSlot 3)).
Definition wf_rep_target_body := SPTAnd (SPTSlot 0) (SPTAnd (SPTSlot 2) (SPTSlot 3)).

Lemma wf_rep_body_forward_program : source_prop_program [wf_rep_raw_body] wf_rep_target_body.
Proof.
  unfold wf_rep_raw_body,wf_rep_target_body. apply SPTCI.
  - eapply SPTCE1;eapply SPTCE1;eapply SPTCE2;apply SPTCtx;now left.
  - apply SPTCI.
    + eapply SPTCE1;apply SPTCtx;now left.
    + eapply SPTCE2;eapply SPTCE2;apply SPTCtx;now left.
Qed.
Lemma wf_rep_body_reverse_program :
  source_prop_program [wf_rep_target_body;SPTSlot 1] wf_rep_raw_body.
Proof.
  unfold wf_rep_raw_body,wf_rep_target_body. apply SPTCI.
  - eapply SPTCE1;eapply SPTCE2;apply SPTCtx;now left.
  - apply SPTCI.
    + apply SPTCI.
      * eapply SPTCE1;apply SPTCtx;now left.
      * apply SPTCtx;right;now left.
    + eapply SPTCE2;eapply SPTCE2;apply SPTCtx;now left.
Qed.

Theorem source_full_wf_rep_body_forward M rho k b c n raw target :
  (forall i,source_bounded M (rho i) k) ->context_bounded M b c n k ->
  code_relation M rho (source_prop_expression wf_rep_raw_body) raw ->
  code_relation M rho (source_prop_expression wf_rep_target_body) target ->
  source_full_prv M b c n raw ->source_full_prv M b c n target.
Proof.
  intros HB HC HR HT PR.
  apply (source_prop_program_sound M [wf_rep_raw_body] wf_rep_target_body wf_rep_body_forward_program
    rho k b c n target HB HC);[|exact HT].
  intros a [<-|[]] f HF.
  pose proof (code_relation_functional M _ rho f raw HF HR) as E. now subst f.
Qed.

Theorem source_full_wf_rep_body_reverse M rho k b c n raw target :
  (forall i,source_bounded M (rho i) k) ->context_bounded M b c n k ->
  code_relation M rho (source_prop_expression wf_rep_raw_body) raw ->
  code_relation M rho (source_prop_expression wf_rep_target_body) target ->
  source_full_prv M b c n target ->source_full_prv M b c n (rho 1) ->source_full_prv M b c n raw.
Proof.
  intros HB HC HR HT PT PD.
  apply (source_prop_program_sound M [wf_rep_target_body;SPTSlot 1] wf_rep_raw_body wf_rep_body_reverse_program
    rho k b c n raw HB HC);[|exact HR].
  intros a [<-|[<-|[]]] f HF.
  - pose proof (code_relation_functional M _ rho f target HF HT) as E. now subst f.
  - change (f=rho 1) in HF. now subst f.
Qed.

Print Assumptions source_full_wf_rep_body_forward.
Print Assumptions source_full_wf_rep_body_reverse.
