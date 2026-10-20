(** Opening a universal theorem at the fresh variable preserves an actual
    closed source axiom context. The operation is an ordinary source proof. *)
From PAModel Require Import Model FiniteCoding SetFormulaCodes NumericalSourceFull
  SourceDescriptorProvability SourceClosedContextShift SourceUniversalPropositional.
Unset Implicit Arguments.

Theorem source_descriptor_provable_all_body M T body all :
  sf_relation M SFAll body (zeroM M) all ->source_descriptor_provable M T all ->
  source_descriptor_provable M T body.
Proof.
  intros HAll (b&c&n&HC&HP). exists b,c,n. split;[exact HC|].
  exact (source_full_all_shift M b c n body all b c HAll HP
    (source_closed_context_shift_self M b c n (proj1 HC))).
Qed.

Print Assumptions source_descriptor_provable_all_body.
