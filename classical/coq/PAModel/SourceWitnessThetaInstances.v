(** Actual diagonal and positive-point instances of the same arbitrary
    internal witness_theta. Their output matrix is literally shared by
    checked composition; no assumed substitution equality is used. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes FixedSourceBounds
  SourceBounded NumericalRenamingMaps NumericalSubstitutionMaps NumericalSubstitution
  SourceFiniteNameParameters SourceWitnessThetaRecipe SourceWitnessThetaSubstitution
  SourceWitnessThetaMatrixActions SourceRelativizedSelectors.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Lemma witness_finite_substitution_total M count rho base :exists b c,forall i,
  (i<count)%nat ->substitution_lookup M b c(code_numeral M count) base(code_numeral M i)(rho i).
Proof.
  destruct(source_finite_names_total M count rho(zeroM M)) as(b&c&HR).
  exists b,c. intros i HI.
  pose proof(proj2(fixed_source_numeral_lt_iff M i count) HI) as HLt.
  apply(proj2(substitution_lookup_inside M b c(code_numeral M count) base _ _ HLt)).
  exact(proj1(renaming_lookup_inside M b c(code_numeral M count)(zeroM M) _ _ HLt)(HR i HI)).
Qed.

Definition source_witness_diagonal_map M p delta b c :=forall i,(i<4)%nat ->
  substitution_lookup M b c(code_numeral M 4) delta(code_numeral M i) p.
Definition witness_point_names M p s t i :=match i with
  0=>zeroM M |1=>succM M p |2=>succM M s |S _=>succM M t end.
Definition source_witness_point_map M p s t delta b c :=forall i,(i<4)%nat ->
  substitution_lookup M b c(code_numeral M 4)(succM M delta)(code_numeral M i)
    (witness_point_names M p s t i).
Definition witness_matrix_names M p i :=match i with 0=>zeroM M|S _=>succM M p end.
Definition source_witness_matrix_map M p delta b c :=forall i,(i<2)%nat ->
  substitution_lookup M b c(code_numeral M 2)(succM M delta)(code_numeral M i)
    (witness_matrix_names M p i).

Theorem source_witness_theta_diagonal_point_total M phi bound theta p s t delta :
  source_bounded M phi bound ->source_witness_theta_recipe M phi theta ->
  exists db dc pb pc mb mc diagonal point matrix some pp st diagonalHole pointHole,
    source_witness_diagonal_map M p delta db dc /\source_witness_point_map M p s t delta pb pc /\
    source_witness_matrix_map M p delta mb mc /\
    numerical_substitution M theta db dc(code_numeral M 4) delta diagonal /\
    numerical_substitution M theta pb pc(code_numeral M 4)(succM M delta) point /\
    numerical_substitution M phi mb mc(code_numeral M 2)(succM M delta) matrix /\
    sf_relation M SFEx matrix (zeroM M) some /\sf_relation M SFMember p p pp /\
    sf_relation M SFMember (succM M s)(succM M t) st /\
    source_selector_graph M pp diagonalHole some diagonal /\
    source_selector_graph M st matrix pointHole point.
Proof.
  intros HP HTheta.
  destruct(witness_finite_substitution_total M 4(fun _=>p) delta) as(db&dc&HD).
  destruct(witness_finite_substitution_total M 4(witness_point_names M p s t)(succM M delta)) as(pb&pc&HPoint).
  destruct(witness_finite_substitution_total M 2(witness_matrix_names M p)(succM M delta)) as(mb&mc&HM).
  destruct(numerical_substitution_total M phi mb mc(code_numeral M 2)(succM M delta)) as(matrix&HMatrix).
  destruct(numerical_substitution_total M theta db dc(code_numeral M 4) delta) as(diagonal&HDiagonal).
  destruct(numerical_substitution_total M theta pb pc(code_numeral M 4)(succM M delta)) as(point&HPointSub).
  destruct(source_witness_theta_substitution_selector M phi theta db dc(code_numeral M 4) delta diagonal p p
    HTheta HDiagonal (HD 2 ltac:(lia))(HD 3 ltac:(lia)))
    as(a&b&diagonalHole&lb&lc&ln&candidate&some&pp&HA&HB&HDiagA&HLift&HDiagB&HSome&HPP&HDiagSelector).
  pose proof(source_witness_theta_negative_matrix_action M phi bound b db dc delta p lb lc ln mb mc candidate
    HP HB (HD 1 ltac:(lia)) HLift (HM 0 ltac:(lia))(HM 1 ltac:(lia)) HDiagB) as HCand.
  pose proof(numerical_substitution_functional M phi mb mc(code_numeral M 2)(succM M delta)
    candidate matrix HCand HMatrix) as ECand. subst candidate.
  destruct(source_witness_theta_substitution_selector M phi theta pb pc(code_numeral M 4)(succM M delta)
    point (succM M s)(succM M t) HTheta HPointSub (HPoint 2 ltac:(lia))(HPoint 3 ltac:(lia)))
    as(a'&b'&positive&ub&uc&un&negative&pointHole&st&HA'&HB'&HPointA&HPointLift&HPointB&HPointEx&HST&HPointSelector).
  pose proof(source_witness_theta_positive_matrix_action M phi bound a' pb pc delta p mb mc positive
    HP HA' (HPoint 0 ltac:(lia))(HPoint 1 ltac:(lia))(HM 0 ltac:(lia))(HM 1 ltac:(lia)) HPointA) as HPos.
  pose proof(numerical_substitution_functional M phi mb mc(code_numeral M 2)(succM M delta)
    positive matrix HPos HMatrix) as EPos. subst positive.
  exists db,dc,pb,pc,mb,mc,diagonal,point,matrix,some,pp,st,diagonalHole,pointHole.
  split;[exact HD|]. split;[exact HPoint|]. split;[exact HM|].
  repeat split;assumption.
Qed.

Print Assumptions witness_finite_substitution_total.
Print Assumptions source_witness_theta_diagonal_point_total.
