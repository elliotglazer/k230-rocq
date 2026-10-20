From PAModel Require Import Model SetFormulaCodes SourceBounded NumericalContexts
  NumericalSourceFull.
Unset Implicit Arguments.

Theorem source_full_conjunction_left M b c n a d f :
  sf_relation M SFAnd a d f ->source_full_prv M b c n f ->source_full_prv M b c n a.
Proof.
  intros HG HP. apply (full_source_CE1 M b c n a d f);[|exact HP|exact HG].
  destruct (source_full_prv_wellformed M b c n f HP) as [k [HB HC]].
  exists k. split;[|exact HC].
  exact (proj1 (proj1 (source_bounded_accept_binary M SFAnd a d f k (or_introl eq_refl) HG) HB)).
Qed.

Theorem source_full_conjunction_right M b c n a d f :
  sf_relation M SFAnd a d f ->source_full_prv M b c n f ->source_full_prv M b c n d.
Proof.
  intros HG HP. apply (full_source_CE2 M b c n a d f);[|exact HP|exact HG].
  destruct (source_full_prv_wellformed M b c n f HP) as [k [HB HC]].
  exists k. split;[|exact HC].
  exact (proj2 (proj1 (source_bounded_accept_binary M SFAnd a d f k (or_introl eq_refl) HG) HB)).
Qed.

Print Assumptions source_full_conjunction_left.
Print Assumptions source_full_conjunction_right.
