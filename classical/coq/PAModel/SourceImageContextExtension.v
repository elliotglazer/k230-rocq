(** Keep a preexisting closed target context and an actual proof in it
    when collecting all the source axiom-image contexts. *)
From PAModel Require Import Model NumericalContexts NumericalSourceFull SourceRelativization
  SourceProofWeakening ContextCombination SourceAxiomContexts SourceContextImages SourceImageContextCollection.
Unset Implicit Arguments.

Theorem source_axiom_image_context_collect_extending M T domain b c n eb ec en :
  source_axiom_context M T eb ec en ->
  (forall f g,context_member M b c n f -> source_relativization M domain f g ->
    exists tb tc tn,source_axiom_context M T tb tc tn /\ source_full_prv M tb tc tn g) ->
  exists ub uc un,source_axiom_context M T ub uc un /\
    context_included M eb ec en ub uc un /\ source_context_images M domain b c n ub uc un.
Proof.
  intros HE HLocal.
  destruct (source_axiom_image_context_collect M T domain b c n HLocal) as (tb & tc & tn & HT & HImages).
  destruct (context_union_total M eb ec en tb tc tn) as (ub & uc & un & HU).
  pose proof (source_axiom_context_union M T eb ec en tb tc tn ub uc un HE HT HU) as HUnion.
  exists ub,uc,un. split;[exact HUnion|]. split.
  - exact (context_union_left M eb ec en tb tc tn ub uc un HU).
  - intros f g HF HG.
    apply (source_full_prv_weaken_bounded M tb tc tn ub uc un g (zeroM M));[| |exact (proj1 HUnion)].
    + exact (HImages f g HF HG).
    + exact (context_union_right M eb ec en tb tc tn ub uc un HU).
Qed.

Theorem source_axiom_image_context_collect_with_proof M T domain b c n eb ec en p :
  source_axiom_context M T eb ec en -> source_full_prv M eb ec en p ->
  (forall f g,context_member M b c n f -> source_relativization M domain f g ->
    exists tb tc tn,source_axiom_context M T tb tc tn /\ source_full_prv M tb tc tn g) ->
  exists ub uc un,source_axiom_context M T ub uc un /\
    source_full_prv M ub uc un p /\ source_context_images M domain b c n ub uc un.
Proof.
  intros HE P HLocal.
  destruct (source_axiom_image_context_collect_extending M T domain b c n eb ec en HE HLocal)
    as (ub & uc & un & HU & HI & HImages).
  exists ub,uc,un. split;[exact HU|]. split;[|exact HImages].
  exact (source_full_prv_weaken_bounded M eb ec en ub uc un p (zeroM M) P HI (proj1 HU)).
Qed.

Print Assumptions source_axiom_image_context_collect_extending.
Print Assumptions source_axiom_image_context_collect_with_proof.
