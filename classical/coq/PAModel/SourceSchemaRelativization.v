(** Exact arithmetic relativization of finite schema constructors around
    arbitrary internal formula holes. No source-provability premise occurs. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SetCodeDescent
  SetSchemaConstructors QuotationRules QuotationSchemaSkeleton
  SourceRelativizationRules SourceRelativization SourceRelativizationFunctionality
  SourceRelativizationRenaming SourceBounded SchemaRenamingDescriptors.
Unset Implicit Arguments.

Fixpoint skeleton_relative_code (s:source_skeleton) : code_expr :=
  match s with
  | SkeletonHole i => CEvar (S i)
  | SkeletonFalse => CEconst 0
  | SkeletonAtom equality i j =>
      E_sf (quotation_source_atom equality) (CEconst i) (CEconst j)
  | SkeletonBinary op a b =>
      E_sf (skeleton_head op) (skeleton_relative_code a) (skeleton_relative_code b)
  | SkeletonQuantifier universal a =>
      E_sf (sr_source_quantifier universal)
        (E_sf (if universal then SFImpl else SFAnd) (CEvar 0) (skeleton_relative_code a))
        (CEconst 0)
  end.
Definition skeleton_relative_environment {A} (d:A) (holes:nat->A) i :=
  match i with 0=>d|S j=>holes j end.

Theorem skeleton_source_relativization M s : forall d sources outputs f rf,
  (forall i,source_relativization M d (sources i) (outputs i)) ->
  code_relation M sources (skeleton_code s) f ->
  code_relation M (skeleton_relative_environment d outputs) (skeleton_relative_code s) rf ->
  source_relativization M d f rf.
Proof.
  induction s as [i| |equality i j|op a IHa b IHb|universal a IH];
    intros d sources outputs f rf HH HF HR.
  - change (f=sources i) in HF. change (rf=outputs i) in HR. subst f rf. apply HH.
  - change (f=zeroM M) in HF. change (rf=zeroM M) in HR. subst f rf.
    apply source_relativization_falsity.
  - assert (HS:sf_relation M (quotation_source_atom equality)
        (code_numeral M i) (code_numeral M j) f).
    { exact (proj1 (skeleton_source_relation M sources (quotation_source_atom equality)
        (CEconst i) (CEconst j) _ _ f eq_refl eq_refl) HF). }
    assert (HT:sf_relation M (quotation_source_atom equality)
        (code_numeral M i) (code_numeral M j) rf).
    { exact (proj1 (skeleton_source_relation M (skeleton_relative_environment d outputs)
        (quotation_source_atom equality) (CEconst i) (CEconst j) _ _ rf eq_refl eq_refl) HR). }
    pose proof (sf_relation_functional M _ _ _ f rf HS HT) as E. subst rf.
    apply (source_relativization_atom M d (quotation_source_atom equality) (code_numeral M i) (code_numeral M j) f).
    + destruct equality;[right|left];reflexivity.
    + exact HS.
  - destruct (code_relation_total M (skeleton_code a) sources) as [x HX].
    destruct (code_relation_total M (skeleton_code b) sources) as [y HY].
    destruct (code_relation_total M (skeleton_relative_code a)
      (skeleton_relative_environment d outputs)) as [rx HRX].
    destruct (code_relation_total M (skeleton_relative_code b)
      (skeleton_relative_environment d outputs)) as [ry HRY].
    apply (source_relativization_binary M d (skeleton_head op) x y f rx ry rf).
    + destruct op;unfold skeleton_head;unfold sf_binary;auto.
    + exact (proj1 (skeleton_source_relation M sources (skeleton_head op)
        (skeleton_code a) (skeleton_code b) x y f HX HY) HF).
    + exact (IHa d sources outputs x rx HH HX HRX).
    + exact (IHb d sources outputs y ry HH HY HRY).
    + exact (proj1 (skeleton_source_relation M (skeleton_relative_environment d outputs)
        (skeleton_head op) (skeleton_relative_code a) (skeleton_relative_code b)
        rx ry rf HRX HRY) HR).
  - destruct (code_relation_total M (skeleton_code a) sources) as [x HX].
    destruct (code_relation_total M (skeleton_relative_code a)
      (skeleton_relative_environment d outputs)) as [rx HRX].
    destruct (code_relation_total M
      (E_sf (if universal then SFImpl else SFAnd) (CEvar 0) (skeleton_relative_code a))
      (skeleton_relative_environment d outputs)) as [mid HM].
    apply (source_relativization_quantifier M d universal x f rx rf).
    + exact (proj1 (skeleton_source_relation M sources (sr_source_quantifier universal)
        (skeleton_code a) (CEconst 0) x (zeroM M) f HX eq_refl) HF).
    + exact (IH d sources outputs x rx HH HX HRX).
    + exists mid. split.
      * exact (proj1 (skeleton_source_relation M (skeleton_relative_environment d outputs)
          (if universal then SFImpl else SFAnd) (CEvar 0) (skeleton_relative_code a)
          d rx mid eq_refl HRX) HM).
      * exact (proj1 (skeleton_source_relation M (skeleton_relative_environment d outputs)
          (sr_source_quantifier universal)
          (E_sf (if universal then SFImpl else SFAnd) (CEvar 0) (skeleton_relative_code a))
          (CEconst 0) mid (zeroM M) rf HM eq_refl) HR).
Qed.

Definition sf_relative_separation_constructor M d rbody rf :=
  code_relation M (skeleton_relative_environment d (fun _=>rbody))
    (skeleton_relative_code separation_skeleton) rf.
Definition sf_relative_replacement_constructor M d ra rb rc rf :=
  code_relation M (skeleton_relative_environment d (schema_env3 ra rb rc))
    (skeleton_relative_code replacement_skeleton) rf.

Theorem source_separation_constructor_relativization M d body rbody f rf :
  source_relativization M d body rbody -> sf_separation_constructor M body f ->
  sf_relative_separation_constructor M d rbody rf -> source_relativization M d f rf.
Proof.
  intros HB HF HR. apply (skeleton_source_relativization M separation_skeleton d
    (fun _=>body) (fun _=>rbody) f rf);[intro i;exact HB|exact HF|exact HR].
Qed.

Theorem source_replacement_constructor_relativization M d a b c ra rb rc f rf :
  source_relativization M d a ra -> source_relativization M d b rb ->
  source_relativization M d c rc -> sf_replacement_constructor M a b c f ->
  sf_relative_replacement_constructor M d ra rb rc rf -> source_relativization M d f rf.
Proof.
  intros HA HB HC HF HR. apply (skeleton_source_relativization M replacement_skeleton d
    (schema_env3 a b c) (schema_env3 ra rb rc) f rf);[|exact HF|exact HR].
  intros [|[|i]];[exact HA|exact HB|exact HC].
Qed.

Theorem source_relativization_schema_renaming M d f rf s body rbody :
  source_bounded M d (code_numeral M 1) -> source_relativization M d f rf ->
  schema_renaming M s f body -> schema_renaming M s rf rbody ->
  source_relativization M d body rbody.
Proof.
  intros HD HR HB HRB.
  exact (source_relativization_renaming M d f rf _ _ _ _ body rbody HD HR HB HRB).
Qed.

Print Assumptions skeleton_source_relativization.
Print Assumptions source_separation_constructor_relativization.
Print Assumptions source_replacement_constructor_relativization.
Print Assumptions source_relativization_schema_renaming.
