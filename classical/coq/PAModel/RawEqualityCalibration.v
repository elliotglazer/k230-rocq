(** Arithmetic calibration of the finite three-atom implication skeleton.
    The variable-name map and all raw/source outputs are internal codes. *)
From PAModel Require Import Model CodeExpressions CodeDescent NumericalProofs SetFormulaCodes SetCodeDescent
  NumericalRenamingMaps NumericalRenaming SourceNumeralLift RawSourceImage
  RawSourceImageInversion RawSourcePropositional.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Definition equality_row_atom M (equal:bool) a b f :=
  if equal then equality_graph M a b f else membership_graph M a b f.
Definition equality_row_head (equal:bool) := if equal then SFEqual else SFMember.

Lemma equality_row_atom_nonzero M equal a b f : equality_row_atom M equal a b f -> f<>zeroM M.
Proof.
  destruct equal;intro H;[exact (raw_positive_tag_nonzero M 3 a b f ltac:(lia) H)|
    exact (raw_positive_tag_nonzero M 1 a b f ltac:(lia) H)].
Qed.
Lemma equality_row_atom_image M equal a b f s :
  equality_row_atom M equal a b f -> raw_source_image M f s ->
  sf_relation M (equality_row_head equal) a b s.
Proof.
  destruct equal;[exact (raw_source_equal_inv M a b f s)|exact (raw_source_member_inv M a b f s)].
Qed.
Lemma equality_row_atom_rename M equal i j a b f s p q n delta :
  equality_row_atom M equal a b f -> raw_source_image M f s ->
  renaming_lookup M p q n delta (code_numeral M i) a ->
  renaming_lookup M p q n delta (code_numeral M j) b ->
  numerical_renaming M (code_numeral M (sf_make (equality_row_head equal) i j)) p q n delta s.
Proof.
  intros HA HS HI HJ. pose proof (equality_row_atom_image M equal a b f s HA HS) as HAtom.
  destruct equal.
  - apply (proj2 (numerical_renaming_equal M _ _ _ p q n delta s (sf_make_numeral M SFEqual i j))).
    exists a,b. auto.
  - apply (proj2 (numerical_renaming_member M _ _ _ p q n delta s (sf_make_numeral M SFMember i j))).
    exists a,b. auto.
Qed.

Lemma raw_implication_nonzero_consequent M a b f :
  b<>zeroM M -> implication_graph M a b f -> f<>zeroM M.
Proof. intros HB HI ->. exact (HB (proj2 (raw_zero_implication_arguments M a b HI))). Qed.

Theorem raw_three_atom_implication_rename M eq1 eq2 eq3
    i1 j1 i2 j2 i3 j3 a1 b1 a2 b2 a3 b3 atom1 atom2 atom3 inner raw out p q n delta :
  equality_row_atom M eq1 a1 b1 atom1 -> equality_row_atom M eq2 a2 b2 atom2 ->
  equality_row_atom M eq3 a3 b3 atom3 -> implication_graph M atom2 atom3 inner ->
  implication_graph M atom1 inner raw -> raw_source_image M raw out ->
  renaming_lookup M p q n delta (code_numeral M i1) a1 ->
  renaming_lookup M p q n delta (code_numeral M j1) b1 ->
  renaming_lookup M p q n delta (code_numeral M i2) a2 ->
  renaming_lookup M p q n delta (code_numeral M j2) b2 ->
  renaming_lookup M p q n delta (code_numeral M i3) a3 ->
  renaming_lookup M p q n delta (code_numeral M j3) b3 ->
  numerical_renaming M (code_numeral M (sf_make SFImpl (sf_make (equality_row_head eq1) i1 j1)
    (sf_make SFImpl (sf_make (equality_row_head eq2) i2 j2)
      (sf_make (equality_row_head eq3) i3 j3)))) p q n delta out.
Proof.
  intros HA1 HA2 HA3 HInner HRaw HOut HI1 HJ1 HI2 HJ2 HI3 HJ3.
  pose proof (raw_implication_nonzero_consequent M atom2 atom3 inner
    (equality_row_atom_nonzero M eq3 a3 b3 atom3 HA3) HInner) as HIN.
  pose proof (raw_implication_nonzero_consequent M atom1 inner raw HIN HRaw) as HRN.
  destruct (raw_source_implication_inv M atom1 inner raw out HRN HRaw HOut)
    as (s1&sin&H1&HIn&HImpl).
  destruct (raw_source_implication_inv M atom2 atom3 inner sin HIN HInner HIn)
    as (s2&s3&H2&H3&HImplIn).
  apply (proj2 (numerical_renaming_binary M SFImpl _ _ _ p q n delta out
    ltac:(unfold sf_binary;auto) (sf_make_numeral M SFImpl _ _))).
  exists s1,sin. split.
  - exact (equality_row_atom_rename M eq1 i1 j1 a1 b1 atom1 s1 p q n delta HA1 H1 HI1 HJ1).
  - split;[|exact HImpl].
    apply (proj2 (numerical_renaming_binary M SFImpl _ _ _ p q n delta sin
      ltac:(unfold sf_binary;auto) (sf_make_numeral M SFImpl _ _))).
    exists s2,s3. split.
    + exact (equality_row_atom_rename M eq2 i2 j2 a2 b2 atom2 s2 p q n delta HA2 H2 HI2 HJ2).
    + split;[|exact HImplIn].
      exact (equality_row_atom_rename M eq3 i3 j3 a3 b3 atom3 s3 p q n delta HA3 H3 HI3 HJ3).
Qed.

Print Assumptions raw_three_atom_implication_rename.
