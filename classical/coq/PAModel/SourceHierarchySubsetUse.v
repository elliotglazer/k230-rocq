(** Apply the exact actual hierarchy-subset law in any local context. *)
From PAModel Require Import Model CodeExpressions SourcePropositionalTemplates SourcePropositionalRebase
  SourceHierarchySubsetShell NumericalSourceFull SourceDerivedRules.
Unset Implicit Arguments.

Theorem source_full_hierarchy_subset_use M b c n d e u v od oe subset ld le result law :
  source_hierarchy_subset_shell M d e u v od oe subset ld le result law ->
  source_full_prv M b c n law ->source_full_prv M b c n od ->source_full_prv M b c n oe ->
  source_full_prv M b c n subset ->source_full_prv M b c n ld ->source_full_prv M b c n le ->
  source_full_prv M b c n result.
Proof.
  intros (_&_&_&_&_&_&HLaw) PLaw PD PE PS PLD PLE.
  unfold source_hierarchy_subset_template,source_prop_expression in HLaw.
  destruct (schema_expression_split M _ _ _ _ law HLaw) as (a&t1&HA&HT1&H0).
  change (a=od) in HA. subst a.
  destruct (schema_expression_split M _ _ _ _ t1 HT1) as (a&t2&HA&HT2&H1).
  change (a=oe) in HA. subst a.
  destruct (schema_expression_split M _ _ _ _ t2 HT2) as (a&t3&HA&HT3&H2).
  change (a=subset) in HA. subst a.
  destruct (schema_expression_split M _ _ _ _ t3 HT3) as (a&t4&HA&HT4&H3).
  change (a=ld) in HA. subst a.
  destruct (schema_expression_split M _ _ _ _ t4 HT4) as (a&r&HA&HR&H4).
  change (a=le) in HA. change (r=result) in HR. subst a r.
  pose proof (source_full_modus_ponens M b c n od t1 law H0 PLaw PD) as P1.
  pose proof (source_full_modus_ponens M b c n oe t2 t1 H1 P1 PE) as P2.
  pose proof (source_full_modus_ponens M b c n subset t3 t2 H2 P2 PS) as P3.
  pose proof (source_full_modus_ponens M b c n ld t4 t3 H3 P3 PLD) as P4.
  exact (source_full_modus_ponens M b c n le result t4 H4 P4 PLE).
Qed.

Print Assumptions source_full_hierarchy_subset_use.
