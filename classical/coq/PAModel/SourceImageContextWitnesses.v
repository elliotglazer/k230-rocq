From PAModel Require Import Model NumericalContexts NumericalSourceFull SourceRelativization
  SourceRelativizationFunctionality SourceAxiomContexts SourceContextImages
  SourceImageContextCollection SourceImageContextExtension.
Unset Implicit Arguments.

Theorem source_axiom_image_context_collect_from_witnesses M T domain b c n :
  (forall f,context_member M b c n f -> exists g tb tc tn,
    source_relativization M domain f g /\ source_axiom_context M T tb tc tn /\ source_full_prv M tb tc tn g) ->
  exists ub uc un,source_axiom_context M T ub uc un /\ source_context_images M domain b c n ub uc un.
Proof.
  intro H. apply source_axiom_image_context_collect.
  intros f g HF HG. destruct (H f HF) as (h & tb & tc & tn & HH & HT & HP).
  pose proof (source_relativization_functional M f domain h g HH HG) as E. subst h.
  exists tb,tc,tn. auto.
Qed.

Theorem source_axiom_image_context_collect_witnesses_with_proof M T domain b c n eb ec en p :
  source_axiom_context M T eb ec en -> source_full_prv M eb ec en p ->
  (forall f,context_member M b c n f -> exists g tb tc tn,
    source_relativization M domain f g /\ source_axiom_context M T tb tc tn /\ source_full_prv M tb tc tn g) ->
  exists ub uc un,source_axiom_context M T ub uc un /\
    source_full_prv M ub uc un p /\ source_context_images M domain b c n ub uc un.
Proof.
  intros HE P H. apply (source_axiom_image_context_collect_with_proof M T domain b c n eb ec en p HE P).
  intros f g HF HG. destruct (H f HF) as (h & tb & tc & tn & HH & HT & HP).
  pose proof (source_relativization_functional M f domain h g HH HG) as E. subst h.
  exists tb,tc,tn. auto.
Qed.

Print Assumptions source_axiom_image_context_collect_from_witnesses.
Print Assumptions source_axiom_image_context_collect_witnesses_with_proof.
