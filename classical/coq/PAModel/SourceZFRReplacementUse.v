(** Actual uniform source Replacement axiom use. The only mathematical
    input to range-set existence is an ordinary proof of its exact
    functionality formula; axiom recognition and proof construction are
    performed internally. *)
From PAModel Require Import Model FiniteCoding CodeExpressions ProofTemplates SetFormulaCodes
  SourceBounded NumericalZFCAxioms NumericalZFCClosure NumericalSetClosure
  SchemaRenamingDescriptors SetSchemaConstructors SourceSchemaInstanceFormulas
  SourceSetTheoryDescriptors SourceZFRProvability SourceDescriptorClosure
  SourceDescriptorProvability SourcePropositionalRebase SourceFunctionalityShells.
Unset Implicit Arguments.

Theorem source_zfr_replacement_open M phi count a b c raw :
  source_bounded M phi (succM M (succM M count)) ->
  schema_renaming M RepA phi a ->schema_renaming M RepB phi b ->schema_renaming M RepC phi c ->
  sf_replacement_constructor M a b c raw ->source_zfr_provable M raw.
Proof.
  intros HB HA HBB HC HR.
  destruct (all_prefix_total M count raw) as (closed&HClosed).
  assert (HInstance:numerical_replacement_instance M phi count closed).
  { split;[exact HB|]. exists a,b,c,raw. auto. }
  apply (proj1 (source_zfr_descriptor_provable M raw)).
  apply (source_descriptor_provable_prefix_eliminate M ZFRSourceDescriptor count raw closed HClosed).
  apply (source_descriptor_provable_axiom M ZFRSourceDescriptor closed).
  - exact (source_replacement_instance_zfr_axiom M phi count closed HInstance).
  - exact (numerical_replacement_instance_closed M phi count closed HInstance).
Qed.

Theorem source_zfr_replacement_open_total M phi count :
  source_bounded M phi (succM M (succM M count)) ->
  exists a b c raw,schema_renaming M RepA phi a /\schema_renaming M RepB phi b /\
    schema_renaming M RepC phi c /\sf_replacement_constructor M a b c raw /\source_zfr_provable M raw.
Proof.
  intro HB. destruct (schema_renaming_total M RepA phi) as (a&HA).
  destruct (schema_renaming_total M RepB phi) as (b&HBB).
  destruct (schema_renaming_total M RepC phi) as (c&HC).
  destruct (sf_replacement_constructor_total M a b c) as (raw&HR).
  exists a,b,c,raw. split;[exact HA|]. split;[exact HBB|]. split;[exact HC|]. split;[exact HR|].
  exact (source_zfr_replacement_open M phi count a b c raw HB HA HBB HC HR).
Qed.

Definition E_source_replacement_range theta := E_sf_all (E_sf_ex (E_sf_all
  (E_sf_iff (E_sf_mem 0 1) (E_sf_ex (E_sf SFAnd (E_sf_mem 0 3) theta))))).
Definition source_replacement_range_graph M matrix range :=
  code_relation M (fun _=>matrix) (E_source_replacement_range (CEvar 0)) range.

Lemma source_replacement_open_split M a b c raw :
  sf_replacement_constructor M a b c raw ->exists functionality range,
    source_functionality_graph M a b functionality /\source_replacement_range_graph M c range /\
    sf_relation M SFImpl functionality range raw.
Proof.
  intro H. unfold sf_replacement_constructor,E_sf_replacement in H.
  destruct (schema_expression_split M _ SFImpl _ _ raw H) as (functionality&range&HF&HR&HImp).
  exists functionality,range. split.
  - assert (HS:forall index,code_relation M (schema_env3 a b c)
      (match index with 0=>CEvar 0|1=>CEvar 1|_=>CEconst 0 end)
      (schema_env3 a b (zeroM M) index)).
    { intros [|[|index]];reflexivity. }
    exact (proj1 (code_subst_graph M (schema_env3 a b c)
      (fun index=>match index with 0=>CEvar 0|1=>CEvar 1|_=>CEconst 0 end)
      (schema_env3 a b (zeroM M)) HS (E_sf_functionality (CEvar 0) (CEvar 1)) functionality) HF).
  - split;[|exact HImp].
    assert (HS:forall index:nat,code_relation M (schema_env3 a b c) (CEvar 2) c).
    { intro index;reflexivity. }
    exact (proj1 (code_subst_graph M (schema_env3 a b c) (fun _=>CEvar 2)
      (fun _=>c) HS (E_source_replacement_range (CEvar 0)) range) HR).
Qed.

Theorem source_zfr_replacement_range M phi count a b c functionality :
  source_bounded M phi (succM M (succM M count)) ->
  schema_renaming M RepA phi a ->schema_renaming M RepB phi b ->schema_renaming M RepC phi c ->
  source_functionality_graph M a b functionality ->source_zfr_provable M functionality ->
  exists range,source_replacement_range_graph M c range /\source_zfr_provable M range.
Proof.
  intros HB HA HBB HC HF PF.
  destruct (sf_replacement_constructor_total M a b c) as (raw&HR).
  pose proof (source_zfr_replacement_open M phi count a b c raw HB HA HBB HC HR) as PR.
  destruct (source_replacement_open_split M a b c raw HR) as (f&range&HF'&HRange&HImp).
  pose proof (code_relation_functional M _ _ f functionality HF' HF) as E. subst f.
  exists range. split;[exact HRange|].
  apply (proj1 (source_zfr_descriptor_provable M range)).
  exact (source_descriptor_provable_mp M ZFRSourceDescriptor functionality range raw
    (proj2 (source_zfr_descriptor_provable M functionality) PF)
    (proj2 (source_zfr_descriptor_provable M raw) PR) HImp).
Qed.

Print Assumptions source_zfr_replacement_open.
Print Assumptions source_zfr_replacement_open_total.
Print Assumptions source_replacement_open_split.
Print Assumptions source_zfr_replacement_range.
