From PAModel Require Import Model FiniteCoding NumericalContexts NumericalEnvironments
  NumericalContextRenaming SourceBounded ContextCombination SourceClosedShift.
Unset Implicit Arguments.

Theorem source_closed_context_shift_self M b c n :
  context_bounded M b c n (zeroM M) -> context_shift M b c n b c.
Proof.
  intros HB i f g HI HF HG.
  pose proof (beta_unique M b c i f g HF HG) as E. subst g.
  apply source_closed_shift_self. apply HB. exists i. auto.
Qed.

Theorem source_context_union_bounded M b c n d e m u v l k :
  context_union M b c n d e m u v l ->
  context_bounded M b c n k -> context_bounded M d e m k -> context_bounded M u v l k.
Proof.
  intros [_ HU] HB HD f HF. apply HU in HF. destruct HF as [HF|HF];auto.
Qed.

Print Assumptions source_closed_context_shift_self.
Print Assumptions source_context_union_bounded.
