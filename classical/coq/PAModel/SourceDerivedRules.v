(** Source proof rules whose well-formedness follows from actual premises. *)
From PAModel Require Import Model SetFormulaCodes SourceBounded SourceSequents NumericalSourceFull.
Unset Implicit Arguments.

Theorem source_full_modus_ponens M b c n a d imp :
  sf_relation M SFImpl a d imp -> source_full_prv M b c n imp ->
  source_full_prv M b c n a -> source_full_prv M b c n d.
Proof.
  intros HI PI PA. apply (full_source_IE M b c n a d imp);[|exact PI|exact PA|exact HI].
  destruct (source_full_prv_wellformed M b c n imp PI) as [k [HB HC]].
  exists k. split;[|exact HC].
  exact (proj2 (proj1 (source_bounded_accept_binary M SFImpl a d imp k
    (or_intror (or_intror eq_refl)) HI) HB)).
Qed.

Print Assumptions source_full_modus_ponens.
