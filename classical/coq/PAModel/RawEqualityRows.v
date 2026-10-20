(** Exact raw logical-row calibration against the finite source matrices.
    These graph lemmas do not assume or assert source proof renaming. *)
From PAModel Require Import Model CodeExpressions CodeDescent NumericalProofs ProofTemplates
  NumericalEquality NumericalRenamingMaps NumericalRenaming SetFormulaCodes
  RawSourceImage RawEqualityCalibration FiniteSourceEquality.
Unset Implicit Arguments.

Definition raw_equality_atom_expression (eq:bool) (i j:nat) :=
  if eq then E_weq (CEvar i) (CEvar j) else E_wel (CEvar i) (CEvar j).

Lemma expression_membership_graph M rho X Y x y f :
  code_relation M rho X x -> code_relation M rho Y y ->
  code_relation M rho (E_wel X Y) f -> membership_graph M x y f.
Proof.
  intros HX HY HF. unfold E_wel,E_wim in HF.
  cbn [code_relation] in HF.
  destruct HF as (q&r&[four [p [Hfour [[a [b [Ha [Hb Hp]]]] Hq]]]]&Hr&Hf).
  assert (a=x) by exact (code_relation_functional M X rho a x Ha HX).
  assert (b=y) by exact (code_relation_functional M Y rho b y Hb HY).
  subst a b four r q. exists p. auto.
Qed.

Lemma raw_equality_atom_expression_graph M env eq i j f :
  code_relation M env (raw_equality_atom_expression eq i j) f ->
  equality_row_atom M eq (env i) (env j) f.
Proof.
  destruct eq;intro H.
  - exact (proj1 (expression_equality_graph M env (CEvar i) (CEvar j) _ _ f eq_refl eq_refl) H).
  - exact (expression_membership_graph M env (CEvar i) (CEvar j) _ _ f eq_refl eq_refl H).
Qed.

Theorem raw_three_atom_expression_rename M env eq1 eq2 eq3 i1 j1 i2 j2 i3 j3 raw out p q n delta :
  code_relation M env
    (E_wim (raw_equality_atom_expression eq1 i1 j1)
      (E_wim (raw_equality_atom_expression eq2 i2 j2) (raw_equality_atom_expression eq3 i3 j3))) raw ->
  raw_source_image M raw out ->
  renaming_lookup M p q n delta (code_numeral M i1) (env i1) ->
  renaming_lookup M p q n delta (code_numeral M j1) (env j1) ->
  renaming_lookup M p q n delta (code_numeral M i2) (env i2) ->
  renaming_lookup M p q n delta (code_numeral M j2) (env j2) ->
  renaming_lookup M p q n delta (code_numeral M i3) (env i3) ->
  renaming_lookup M p q n delta (code_numeral M j3) (env j3) ->
  numerical_renaming M (code_numeral M (sf_make SFImpl (sf_make (equality_row_head eq1) i1 j1)
    (sf_make SFImpl (sf_make (equality_row_head eq2) i2 j2)
      (sf_make (equality_row_head eq3) i3 j3)))) p q n delta out.
Proof.
  intros HR HO HI1 HJ1 HI2 HJ2 HI3 HJ3.
  destruct (code_relation_total M (raw_equality_atom_expression eq1 i1 j1) env) as [a1 HA1].
  destruct (code_relation_total M (raw_equality_atom_expression eq2 i2 j2) env) as [a2 HA2].
  destruct (code_relation_total M (raw_equality_atom_expression eq3 i3 j3) env) as [a3 HA3].
  destruct (code_relation_total M (E_wim (raw_equality_atom_expression eq2 i2 j2)
    (raw_equality_atom_expression eq3 i3 j3)) env) as [inside HIn].
  apply (raw_three_atom_implication_rename M eq1 eq2 eq3 i1 j1 i2 j2 i3 j3
    (env i1) (env j1) (env i2) (env j2) (env i3) (env j3) a1 a2 a3 inside raw out p q n delta).
  - exact (raw_equality_atom_expression_graph M env eq1 i1 j1 a1 HA1).
  - exact (raw_equality_atom_expression_graph M env eq2 i2 j2 a2 HA2).
  - exact (raw_equality_atom_expression_graph M env eq3 i3 j3 a3 HA3).
  - exact (expression_implication_graph M env _ _ a2 a3 inside HA2 HA3 HIn).
  - exact (expression_implication_graph M env _ _ a1 inside raw HA1 HIn HR).
  - exact HO.
  - exact HI1.
  - exact HJ1.
  - exact HI2.
  - exact HJ2.
  - exact HI3.
  - exact HJ3.
Qed.

Definition raw_equality_row_expression row :=
  match row with FER3=>code_row3 | FER5=>code_row5 | FER7=>code_row7 end.

Theorem raw_equality_row_renaming M row env raw out p q n delta :
  code_relation M env (raw_equality_row_expression row) raw -> raw_source_image M raw out ->
  renaming_lookup M p q n delta (code_numeral M 0) (env 0) ->
  renaming_lookup M p q n delta (code_numeral M 1) (env 1) ->
  renaming_lookup M p q n delta (code_numeral M 2) (env 2) ->
  numerical_renaming M (code_numeral M (sf_encode (finite_equality_matrix row))) p q n delta out.
Proof.
  intros HR HO H0 H1 H2. destruct row.
  - exact (raw_three_atom_expression_rename M env true false false 0 1 2 0 2 1
      raw out p q n delta HR HO H0 H1 H2 H0 H2 H1).
  - exact (raw_three_atom_expression_rename M env true false false 2 0 2 1 0 1
      raw out p q n delta HR HO H2 H0 H2 H1 H0 H1).
  - exact (raw_three_atom_expression_rename M env true true true 2 0 2 1 0 1
      raw out p q n delta HR HO H2 H0 H2 H1 H0 H1).
Qed.

Print Assumptions raw_equality_row_renaming.
