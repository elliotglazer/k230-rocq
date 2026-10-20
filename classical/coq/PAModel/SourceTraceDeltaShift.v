(** Shifting an actual trace profile increments its parameter tail and
    container names. The arbitrary matrix is transported by proved internal
    substitution composition, including both surviving binders. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes
  SourceBounded SourceFiniteCutoffShift SourceTraceMatrixAlignment SourceTraceProfileShell
  NumericalRenamingMaps NumericalRenaming NumericalSubstitutionMaps NumericalSubstitution
  RenamingSubstitution NumericalContextRenaming SourceQuantifierRules.
Unset Implicit Arguments.

Theorem source_trace_delta_shape_shift M phi k delta matrix atom body theta b
    rb rc rn theta' :
  source_bounded M phi k ->
  numerical_renaming M phi (code_numeral M 3) (code_numeral M 1) (code_numeral M 2) delta matrix ->
  sf_relation M SFMember (zeroM M) (succM M (succM M b)) atom ->
  sf_relation M SFAnd atom matrix body ->sf_relation M SFEx body (zeroM M) theta ->
  renaming_lift M (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1) rb rc rn ->
  numerical_renaming M theta rb rc rn (code_numeral M 1) theta' ->
  exists atom' matrix' body',
    numerical_renaming M phi (code_numeral M 3) (code_numeral M 1) (code_numeral M 2)
      (succM M delta) matrix' /\
    sf_relation M SFMember (zeroM M) (succM M (succM M (succM M b))) atom' /\
    sf_relation M SFAnd atom' matrix' body' /\sf_relation M SFEx body' (zeroM M) theta'.
Proof.
  intros HP HM HA HB HE HL1 HR.
  destruct (proj1 (numerical_renaming_quantifier M false body theta rb rc rn
    (code_numeral M 1) theta' HE) HR) as [sb [sc [sn [body' [HL2 [HRBody HEx']]]]]].
  destruct (proj1 (numerical_renaming_binary M SFAnd atom matrix body sb sc sn
    (code_numeral M 1) body' (or_introl eq_refl) HB) HRBody)
    as [atom' [matrix' [HRAtom [HRMatrix HAnd']]]].
  assert (HMap1:source_cutoff_shift_map M 1 rb rc rn).
  { exists (zeroM M),(zeroM M),(zeroM M). split;[repeat split;reflexivity|].
    pose proof (proj1 (renaming_substitution_lift M (zeroM M) (zeroM M) (zeroM M)
      (code_numeral M 1) rb rc rn) HL1) as H.
    now rewrite Arithmetic.add_zero in H. }
  assert (HMap2:source_cutoff_shift_map M 2 sb sc sn).
  { exists rb,rc,rn. split;[exact HMap1|].
    pose proof (proj1 (renaming_substitution_lift M rb rc rn (code_numeral M 1) sb sc sn) HL2) as H.
    rewrite (proj1 HL1) in H |- *. cbn [code_numeral] in H.
    now rewrite Arithmetic.add_succ,Arithmetic.add_zero in H. }
  assert (HShiftMatrix:source_cutoff_shift M 2 matrix matrix').
  { exists sb,sc,sn. split;[exact HMap2|].
    pose proof (proj1 (numerical_renaming_substitution M matrix sb sc sn
      (code_numeral M 1) matrix') HRMatrix) as H.
    rewrite (proj1 HL2),(proj1 HL1) in H |- *. cbn [code_numeral] in H.
    now rewrite !Arithmetic.add_succ,Arithmetic.add_zero in H. }
  pose proof (source_swapped_cutoff_two_increment M phi matrix matrix' delta k HP HM HShiftMatrix) as HMatrix'.
  destruct (proj1 (numerical_renaming_member M (zeroM M) (succM M (succM M b)) atom
    sb sc sn (code_numeral M 1) atom' HA) HRAtom) as [u [v [HU [HV HAtom']]]].
  apply (proj1 (renaming_lift_head M rb rc rn (code_numeral M 1) sb sc sn u HL2)) in HU.
  subst u.
  assert (HV':renaming_lookup M sb sc sn (code_numeral M 1)
    (succM M (succM M b)) (succM M (succM M (succM M b)))).
  { apply (proj2 (renaming_lift_tail M rb rc rn (code_numeral M 1) sb sc sn
      (succM M b) (succM M (succM M b)) HL2)).
    apply (proj2 (renaming_lift_tail M (zeroM M) (zeroM M) (zeroM M)
      (code_numeral M 1) rb rc rn b (succM M b) HL1)).
    apply context_shift_lookup. reflexivity. }
  pose proof (renaming_lookup_functional M sb sc sn (code_numeral M 1)
    (succM M (succM M b)) v _ HV HV') as E. subst v.
  exists atom',matrix',body'. auto.
Qed.

Theorem source_trace_delta_profile_shift M phi k delta c b profile theta atom matrix body shifted :
  source_bounded M phi k ->
  numerical_renaming M phi (code_numeral M 3) (code_numeral M 1) (code_numeral M 2) delta matrix ->
  sf_relation M SFMember (zeroM M) (succM M (succM M b)) atom ->
  sf_relation M SFAnd atom matrix body ->sf_relation M SFEx body (zeroM M) theta ->
  source_trace_profile_shell M theta c b profile ->source_formula_shift M profile shifted ->
  exists theta' atom' matrix' body',
    numerical_renaming M phi (code_numeral M 3) (code_numeral M 1) (code_numeral M 2)
      (succM M delta) matrix' /\
    sf_relation M SFMember (zeroM M) (succM M (succM M (succM M b))) atom' /\
    sf_relation M SFAnd atom' matrix' body' /\sf_relation M SFEx body' (zeroM M) theta' /\
    source_trace_profile_shell M theta' (succM M c) (succM M b) shifted.
Proof.
  intros HP HM HA HB HE HProfile HS.
  destruct (source_trace_profile_shell_shift M theta c b profile shifted HProfile HS)
    as [theta' [rb [rc [rn [HL [HR HProfile']]]]]].
  destruct (source_trace_delta_shape_shift M phi k delta matrix atom body theta b rb rc rn theta'
    HP HM HA HB HE HL HR) as [atom' [matrix' [body' [HM' [HA' [HB' HE']]]]]].
  exists theta',atom',matrix',body'. repeat split;assumption.
Qed.

Print Assumptions source_trace_delta_shape_shift.
Print Assumptions source_trace_delta_profile_shift.
