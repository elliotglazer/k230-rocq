From PAModel Require Import Model SourceBounded NumericalContexts NumericalEnvironments
  NumericalSourceFull SourceContextTransport SourceProofWeakening.
Unset Implicit Arguments.

Theorem source_full_cons_weaken M b c n a u v l k f :
  environment_cons M b c n a u v l ->context_bounded M u v l k ->
  source_full_prv M b c n f ->source_full_prv M u v l f.
Proof.
  intros HH HC HP. apply (source_full_prv_weaken_bounded M b c n u v l f k HP);[|exact HC].
  intros g HG. apply (proj2 (context_member_cons M b c n a u v l g HH)). now right.
Qed.

Theorem source_full_cons_head M b c n a u v l k :
  environment_cons M b c n a u v l ->source_bounded M a k ->context_bounded M u v l k ->
  source_full_prv M u v l a.
Proof.
  intros HH HA HC. apply (full_source_Ctx M u v l a).
  - exists k. now split.
  - apply (proj2 (context_member_cons M b c n a u v l a HH)). now left.
Qed.

Print Assumptions source_full_cons_weaken.
Print Assumptions source_full_cons_head.
