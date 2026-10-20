(** Produce the actual open Separation axiom proof for an arbitrary
    internally coded matrix and closure length. No source proof-search,
    standard-model decoding, or reflection premise is assumed. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SourceBounded NumericalZFCAxioms NumericalZFCClosure NumericalSetClosure
  SchemaRenamingDescriptors SetSchemaConstructors SourceSchemaInstanceFormulas
  SourceSetTheoryDescriptors SourceZFRProvability SourceDescriptorClosure
  SourceDescriptorProvability.
Unset Implicit Arguments.

Theorem source_zfr_separation_open M phi count body raw :
  source_bounded M phi (succM M count) -> schema_renaming M SepBody phi body ->
  sf_separation_constructor M body raw ->source_zfr_provable M raw.
Proof.
  intros HB HBody HRaw.
  destruct (all_prefix_total M count raw) as [closed HClosed].
  assert (HA:numerical_separation_instance M phi count closed).
  { split;[exact HB|]. exists body,raw. auto. }
  apply (proj1 (source_zfr_descriptor_provable M raw)).
  apply (source_descriptor_provable_prefix_eliminate M ZFRSourceDescriptor count raw closed HClosed).
  apply (source_descriptor_provable_axiom M ZFRSourceDescriptor closed).
  - exact (source_separation_instance_zfr_axiom M phi count closed HA).
  - exact (numerical_separation_instance_closed M phi count closed HA).
Qed.

Theorem source_zfr_separation_open_total M phi count :
  source_bounded M phi (succM M count) ->
  exists body raw,schema_renaming M SepBody phi body /\
    sf_separation_constructor M body raw /\ source_zfr_provable M raw.
Proof.
  intro HB. destruct (schema_renaming_total M SepBody phi) as [body HBody].
  destruct (sf_separation_constructor_total M body) as [raw HRaw].
  exists body,raw. split;[exact HBody|]. split;[exact HRaw|].
  exact (source_zfr_separation_open M phi count body raw HB HBody HRaw).
Qed.

Print Assumptions source_zfr_separation_open.
Print Assumptions source_zfr_separation_open_total.
