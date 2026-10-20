(** Invert the actual RepA/RepB renaming of the least-ordinal relation.
    The two predicate codes are never decoded. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  NumericalRenamingMaps NumericalRenaming NumericalInstantiation SourceDomainInstanceRenaming
  SchemaRenamingDescriptors SourceOrdinalCrossInstantiation.
Unset Implicit Arguments.

Definition oc_side_value M (side:bool) := code_numeral M (if side then 1 else 0).
Lemma oc_side_second_lookup M side :renaming_lookup M (code_numeral M (oc_side_dividend side))
  (code_numeral M 3) (code_numeral M 2) (code_numeral M 1) (code_numeral M 1) (oc_side_value M side).
Proof.
  destruct side;[change (schema_lookup M RepA (code_numeral M 1) (code_numeral M 1))|
    change (schema_lookup M RepB (code_numeral M 1) (code_numeral M 0))];
    apply (proj2 (schema_lookup_second M _ _));reflexivity.
Qed.

Theorem source_oc_side_payload M side ordinal ord1 swapped shifted atom neg point tail inner oc sideout :
  source_bounded M ordinal (code_numeral M 1) ->numerical_instantiation M ordinal (code_numeral M 1) ord1 ->
  sf_relation M SFMember (zeroM M) (code_numeral M 2) atom ->sf_relation M SFImpl shifted (zeroM M) neg ->
  sf_relation M SFImpl atom neg point ->sf_relation M SFAll point (zeroM M) tail ->
  sf_relation M SFAnd ord1 swapped inner ->sf_relation M SFAnd inner tail oc ->
  oc_side_renaming M side oc sideout ->
  exists ord pred all tag matrix sideatom sideneg sidepoint rb rc rn,
    numerical_instantiation M ordinal (oc_side_value M side) ord /\
    oc_side_renaming M side swapped pred /\sf_relation M SFAnd ord pred tag /\
    sf_relation M SFAnd tag all sideout /\sf_relation M SFAll sidepoint (zeroM M) all /\
    sf_relation M SFMember (zeroM M) (succM M (oc_side_value M side)) sideatom /\
    sf_relation M SFImpl matrix (zeroM M) sideneg /\sf_relation M SFImpl sideatom sideneg sidepoint /\
    renaming_lift M (code_numeral M (oc_side_dividend side)) (code_numeral M 3)
      (code_numeral M 2) (code_numeral M 1) rb rc rn /\
    numerical_renaming M shifted rb rc rn (code_numeral M 1) matrix.
Proof.
  intros HD HOrd HA HN HP HT HI HO HR.
  destruct (proj1 (numerical_renaming_binary M SFAnd inner tail oc _ _ _ _ sideout (or_introl eq_refl) HO) HR)
    as (tag&all&HRI&HRT&HSide).
  destruct (proj1 (numerical_renaming_binary M SFAnd ord1 swapped inner _ _ _ _ tag (or_introl eq_refl) HI) HRI)
    as (ord&pred&HRO&HRP&HTag).
  destruct (proj1 (numerical_renaming_quantifier M true point tail _ _ _ _ all HT) HRT)
    as (rb&rc&rn&sidepoint&HL&HRPoint&HAll).
  destruct (proj1 (numerical_renaming_binary M SFImpl atom neg point rb rc rn _ sidepoint
    (or_intror (or_intror eq_refl)) HP) HRPoint) as (sideatom&sideneg&HRAtom&HRNeg&HPoint).
  destruct (proj1 (numerical_renaming_binary M SFImpl shifted (zeroM M) neg rb rc rn _ sideneg
    (or_intror (or_intror eq_refl)) HN) HRNeg) as (matrix&z&HRMatrix&HRZero&HNeg).
  apply (proj1 (numerical_renaming_invalid M (zeroM M) rb rc rn _ z (or_introl eq_refl))) in HRZero.
  subst z.
  destruct (proj1 (numerical_renaming_member M (zeroM M) (code_numeral M 2) atom rb rc rn _ sideatom HA) HRAtom)
    as (x&y&HX&HY&HAtom).
  apply (proj1 (renaming_lift_head M _ _ _ _ rb rc rn x HL)) in HX. subst x.
  destruct (renaming_lift_tail_inv M _ _ _ _ rb rc rn (code_numeral M 1) y HL HY) as (y'&HY'&EY).
  pose proof (renaming_lookup_functional M _ _ _ _ _ y' _ HY' (oc_side_second_lookup M side)) as E.
  subst y' y.
  exists ord,pred,all,tag,matrix,sideatom,sideneg,sidepoint,rb,rc,rn.
  split.
  - exact (source_domain_instance_renaming M ordinal (code_numeral M 1) ord1 _ _ _ _ ord
      (oc_side_value M side) HD HOrd HRO (oc_side_second_lookup M side)).
  - split;[exact HRP|]. split;[exact HTag|]. split;[exact HSide|].
    split;[exact HAll|]. split;[exact HAtom|]. split;[exact HNeg|].
    split;[exact HPoint|]. split;assumption.
Qed.
Print Assumptions source_oc_side_payload.
