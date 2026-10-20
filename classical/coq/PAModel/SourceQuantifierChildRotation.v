(** Exact first Dn rotation of an arbitrary child representation matrix.
    The distinguished child value moves from3 to1; its carrier moves2 to3.
    No matrix is assumed standard and no source provability premise is used. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 NumericalRenamingMaps NumericalRenaming SourceRenamingIdentity SourceRenamingDiamond SourceShiftSpecialization
 SourceDnStep SourceQuantifierMatrixScopes SourceSetRelativization SourceSetRelativizationRenaming.
From FOL.Tennenbaum Require Peano.
Unset Implicit Arguments.
Definition source_quantifier_rotation M b c n:=renaming_lift M
 (code_numeral M 1653)(code_numeral M 6)(code_numeral M 3)(zeroM M)b c n.
Lemma source_quantifier_rotation_three M b c n:source_quantifier_rotation M b c n ->
 renaming_lookup M b c n(zeroM M)(code_numeral M 3)(code_numeral M 1).
Proof.
 intro H. apply(proj2(renaming_lift_tail M _ _ _ _ b c n(code_numeral M 2)(zeroM M)H)).
 apply source_dn_rotate_two.
Qed.
Lemma source_quantifier_rotation_two M b c n:source_quantifier_rotation M b c n ->
 renaming_lookup M b c n(zeroM M)(code_numeral M 2)(code_numeral M 3).
Proof.
 intro H. apply(proj2(renaming_lift_tail M _ _ _ _ b c n(code_numeral M 1)(code_numeral M 2)H)).
 apply source_dn_rotate_one.
Qed.
Lemma source_quantifier_rotation_above M b c n i:source_quantifier_rotation M b c n ->
 renaming_lookup M b c n(zeroM M)(succM M(succM M(succM M(succM M i))))
 (succM M(succM M(succM M(succM M i)))).
Proof.
 intro H. apply(proj2(renaming_lift_tail M _ _ _ _ b c n
  (succM M(succM M(succM M i)))(succM M(succM M(succM M i)))H)).
 apply source_dn_rotate_outside. intro HB.
 change(coding_lt M(succM M(succM M(succM M i)))(succM M(succM M(succM M(zeroM M)))))in HB.
   exact(coding_not_lt_zero M i(proj1(coding_lt_succ_cancel M i(zeroM M))
    (proj1(coding_lt_succ_cancel M(succM M i)(succM M(zeroM M)))
     (proj1(coding_lt_succ_cancel M(succM M(succM M i))(succM M(succM M(zeroM M))))HB)))).
Qed.
Theorem source_quantifier_child_matrix_rotation M f matrix child k b c n:
 source_bounded M f k ->source_quantifier_rotation M b c n ->
 numerical_renaming M f(zeroM M)(zeroM M)(zeroM M)(code_numeral M 3)matrix ->
 source_quantifier_matrix M(code_numeral M 1)f child ->
 numerical_renaming M matrix b c n(zeroM M)child.
Proof.
 intros BF HL HM HC.
 assert(HId:numerical_renaming M f(zeroM M)(zeroM M)(zeroM M)(zeroM M)f).
 { apply(numerical_renaming_identity_on_bound M f _ _ _ _ k BF).
   intros i _. apply source_empty_renaming_lookup. }
 apply(numerical_source_renaming_diamond M f k
  (zeroM M)(zeroM M)(zeroM M)(zeroM M)
  (zeroM M)(zeroM M)(zeroM M)(code_numeral M 3)
  (code_numeral M 1)(code_numeral M 1)(code_numeral M 1)(code_numeral M 3)
  b c n(zeroM M)f matrix child BF HId HM HC).
 intros i j l m HI HJ HCJ HML.
 rewrite(renaming_lookup_functional M _ _ _ _ i j i HJ(source_empty_renaming_lookup M i))in HCJ.
 rewrite(renaming_lookup_functional M _ _ _ _ i l _ HML
  (or_intror(conj(coding_not_lt_zero M i)eq_refl))).
 destruct(@Peano.zero_or_succ(Model.carrier M)(raw_interpretation M)
  (fun ax H rho=>axioms M ax rho H)i)as[->|[q ->]].
 - rewrite(renaming_lookup_functional M _ _ _ _ _ m _ HCJ
    (source_one_role_zero_lookup M(code_numeral M 1)(code_numeral M 3))).
   rewrite Arithmetic.add_zero.
   change(renaming_lookup M b c n(zeroM M)(code_numeral M 3)(code_numeral M 1)).
   exact(source_quantifier_rotation_three M b c n HL).
 - assert(HN:succM M q<>zeroM M)by(exact(fun E=>Model.zero_ne_succ M q(eq_sym E))).
   rewrite(renaming_lookup_functional M _ _ _ _ _ m _ HCJ
    (source_one_role_positive_lookup M(code_numeral M 1)(code_numeral M 3)_ HN)).
   change(renaming_lookup M b c n(zeroM M)(addM M(succM M q)(code_numeral M 3))
    (addM M(succM M q)(code_numeral M 3))).
   replace(addM M(succM M q)(code_numeral M 3))with(succM M(succM M(succM M(succM M q)))).
   + exact(source_quantifier_rotation_above M b c n q HL).
   + rewrite Arithmetic.add_comm. cbn[code_numeral]. now rewrite!Arithmetic.add_succ,Arithmetic.add_zero.
Qed.
Theorem source_quantifier_child_relative_rotation M f matrix relative k b c n:
 source_bounded M f k ->source_quantifier_rotation M b c n ->
 numerical_renaming M f(zeroM M)(zeroM M)(zeroM M)(code_numeral M 3)matrix ->
 source_set_relativization M(code_numeral M 2)matrix relative ->
 exists child childrelative,source_quantifier_matrix M(code_numeral M 1)f child /\
 source_set_relativization M(code_numeral M 3)child childrelative /\
 numerical_renaming M relative b c n(zeroM M)childrelative.
Proof.
 intros BF HL HM HR.
 destruct(numerical_renaming_total M f(code_numeral M 1)(code_numeral M 1)
  (code_numeral M 1)(code_numeral M 3))as(child&HC).
 destruct(numerical_renaming_total M relative b c n(zeroM M))as(childrelative&HCR).
 exists child,childrelative. split;[exact HC|]. split;[|exact HCR].
 apply(source_set_relativization_renaming M(code_numeral M 2)(code_numeral M 3)
  matrix relative b c n(zeroM M)child childrelative
  (source_quantifier_rotation_two M b c n HL)HR
  (source_quantifier_child_matrix_rotation M f matrix child k b c n BF HL HM HC)HCR).
Qed.
Print Assumptions source_quantifier_child_matrix_rotation.
Print Assumptions source_quantifier_child_relative_rotation.
