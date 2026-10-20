(** Reopening the two distinguished roles by the actual prefix [b,a]
    restores the arbitrary original source matrix. This is simultaneous
    capture-avoiding substitution, not informal parameter replacement. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions NumericalProofs
  NumericalEnvironments NumericalRenamingMaps NumericalRenaming NumericalSubstitutionMaps NumericalSubstitution
  NumericalInstantiation RenamingSubstitution SourceBounded SourceRenamingIdentity
  SourceShiftSpecialization SourceRenamingSquare SourceRoleAbstraction
  NumericalSetClosure SourceBoundedCalibration.
Unset Implicit Arguments.

Definition source_role_reopening M a b rb rc :=
  substitution_lookup M rb rc (code_numeral M 2) (zeroM M) (zeroM M) b /\
  substitution_lookup M rb rc (code_numeral M 2) (zeroM M) (code_numeral M 1) a.

Theorem source_role_reopening_total M a b :exists rb rc,source_role_reopening M a b rb rc.
Proof.
  destruct (environment_cons_total M (zeroM M) (zeroM M) (zeroM M) a) as (p&q&n&HOne).
  pose proof (proj1 HOne) as EN. subst n.
  destruct (environment_cons_total M p q (code_numeral M 1) b) as (rb&rc&n&HTwo).
  pose proof (proj1 HTwo) as EN. subst n.
  assert (HZero:environment_lookup M rb rc (code_numeral M 2) (zeroM M) b).
  { exact (proj2 (environment_cons_head M p q (code_numeral M 1) b rb rc (code_numeral M 2) b HTwo) eq_refl). }
  assert (HOne':environment_lookup M rb rc (code_numeral M 2) (code_numeral M 1) a).
  { apply (proj2 (environment_cons_tail M p q (code_numeral M 1) b rb rc (code_numeral M 2)
      (zeroM M) a HTwo)).
    exact (proj2 (environment_cons_head M (zeroM M) (zeroM M) (zeroM M) a p q (code_numeral M 1) a HOne) eq_refl). }
  exists rb,rc. split.
  - apply (proj2 (substitution_lookup_inside M rb rc (code_numeral M 2) (zeroM M) (zeroM M) b
      (coding_zero_lt_succ M (code_numeral M 1)))).
    exact (proj1 (environment_lookup_inside M rb rc (code_numeral M 2) (zeroM M) b
      (coding_zero_lt_succ M (code_numeral M 1))) HZero).
  - apply (proj2 (substitution_lookup_inside M rb rc (code_numeral M 2) (zeroM M) (code_numeral M 1) a
      (coding_lt_succ M (code_numeral M 1)))).
    exact (proj1 (environment_lookup_inside M rb rc (code_numeral M 2) (code_numeral M 1) a
      (coding_lt_succ M (code_numeral M 1))) HOne').
Qed.

Lemma source_role_reopening_tail M rb rc i :
  substitution_lookup M rb rc (code_numeral M 2) (zeroM M) (succM M (succM M i)) i.
Proof.
  right. split.
  - intro H. change (coding_lt M (succM M (succM M i)) (succM M (succM M (zeroM M)))) in H.
    exact (coding_not_lt_zero M i (proj1 (coding_lt_succ_cancel M i (zeroM M))
      (proj1 (coding_lt_succ_cancel M (succM M i) (succM M (zeroM M))) H))).
  - exists i. split.
    + change (succM M (succM M i) = addM M (succM M (succM M (zeroM M))) i).
      now rewrite !Arithmetic.add_succ,Arithmetic.add_zero.
    + symmetry. apply Arithmetic.add_zero.
Qed.

Theorem source_role_reopening_lookup M a b rb rc sb sc i j :
  source_role_map M a b rb rc ->source_role_reopening M a b sb sc ->
  renaming_lookup M rb rc (source_role_length M a b) (code_numeral M 2) i j ->
  substitution_lookup M sb sc (code_numeral M 2) (zeroM M) j i.
Proof.
  intros HM [HB HA] HJ. apply (proj1 (HM i j)) in HJ.
  destruct HJ as [[-> ->]|[_ [[-> ->]|[_ ->]]]];try assumption. apply source_role_reopening_tail.
Qed.

Theorem source_role_reopening_restores M a b phi abstract k rb rc sb sc :
  source_bounded M phi k ->source_role_map M a b rb rc ->
  numerical_renaming M phi rb rc (source_role_length M a b) (code_numeral M 2) abstract ->
  source_role_reopening M a b sb sc ->
  numerical_substitution M abstract sb sc (code_numeral M 2) (zeroM M) phi.
Proof.
  intros HF HM HR HReopen.
  assert (HI:numerical_renaming M phi (zeroM M) (zeroM M) (zeroM M) (zeroM M) phi).
  { apply (numerical_renaming_identity_on_bound M phi _ _ _ _ k HF).
    intros i _. apply source_empty_renaming_lookup. }
  apply (numerical_source_renaming_square M phi k
    (zeroM M) (zeroM M) (zeroM M) (zeroM M)
    rb rc (source_role_length M a b) (code_numeral M 2)
    (zeroM M) (zeroM M) (zeroM M) (zeroM M)
    sb sc (code_numeral M 2) (zeroM M) phi abstract phi HF
    (proj1 (numerical_renaming_empty_substitution M phi _ _ _ phi) HI) HR HI).
  intros i j l m HIbound HJ HJM HL.
  assert (EJ:j=i).
  { exact (substitution_lookup_functional M _ _ _ _ i j i HJ (source_empty_substitution_lookup M i)). }
  subst j.
  assert (EM:m=i).
  { exact (renaming_lookup_functional M _ _ _ _ i m i HJM (source_empty_renaming_lookup M i)). }
  subst m. exact (source_role_reopening_lookup M a b rb rc sb sc i l HM HReopen HL).
Qed.

Theorem source_role_abstraction_reopens M a b phi abstract k :
  source_bounded M phi k ->source_role_abstraction M a b phi abstract ->
  exists sb sc,source_role_reopening M a b sb sc /\
    numerical_substitution M abstract sb sc (code_numeral M 2) (zeroM M) phi.
Proof.
  intros HF (rb&rc&HM&HR). destruct (source_role_reopening_total M a b) as (sb&sc&HS).
  exists sb,sc. split;[exact HS|exact (source_role_reopening_restores M a b phi abstract k rb rc sb sc HF HM HR HS)].
Qed.

Theorem source_role_abstract_closure_total M a b phi k :source_bounded M phi k ->
  exists abstract closed,source_role_abstraction M a b phi abstract /\
    source_bounded M abstract (succM M (succM M k)) /\
    all_prefix M (succM M (succM M k)) abstract closed /\source_bounded M closed (zeroM M).
Proof.
  intro HF. destruct (source_role_abstraction_total M a b phi) as (abstract&HA).
  pose proof (source_role_abstraction_bounded M a b phi abstract k HF HA) as HB.
  destruct (all_prefix_total M (succM M (succM M k)) abstract) as (closed&HC).
  exists abstract,closed. repeat first [assumption|split].
  exact (all_prefix_closes M (succM M (succM M k)) abstract closed HB HC).
Qed.

Print Assumptions source_role_reopening_total.
Print Assumptions source_role_reopening_restores.
Print Assumptions source_role_abstract_closure_total.
