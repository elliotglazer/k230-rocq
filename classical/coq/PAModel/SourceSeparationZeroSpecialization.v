(** Actual outer-All specialization of Separation at variable zero.
    The matrix and all map representations range over the PA model. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SetSchemaConstructors SourceBounded SourceFiniteCutoffShift SchemaRenamingDescriptors
  NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation SourceNumeralLift
  SourcePropositionalTemplates SourceSeparationSubset SourceWFSeparationWitness
  SourceWFSeparationConstructor SourcePropositionalSubstitution SourceSeparationSpecializationMaps.
Unset Implicit Arguments.

Definition E_separation_zero theta :=
  E_sf_ex (E_sf_all (E_sf_iff (E_sf_mem 0 1)
    (E_sf SFAnd (E_sf_mem 0 2) theta))).

Local Opaque source_sep_left_code source_sep_right_code.

Theorem source_separation_zero_specialization M phi body raw p1 k :
  source_bounded M phi k ->
  schema_renaming M SepBody phi body ->
  sf_separation_constructor M body raw ->
  source_cutoff_shift M 1 phi p1 ->
  exists rawbody specialized,
    sf_relation M SFAll rawbody (zeroM M) raw /\
    numerical_instantiation M rawbody (zeroM M) specialized /\
    code_relation M (fun _=>p1) (E_separation_zero (CEvar 0)) specialized.
Proof.
  intros HB HBody HRaw HP.
  unfold sf_separation_constructor,E_sf_separation,E_sf_all,E_sf_ex in HRaw.
  destruct (schema_expression_quantifier_split M _ SFAll _ raw HRaw)
    as [rawbody [HRawBody HRawAll]].
  destruct (schema_expression_quantifier_split M _ SFEx _ rawbody HRawBody)
    as [profile [HProfile HRawEx]].
  destruct (schema_expression_quantifier_split M _ SFAll _ profile HProfile)
    as [point [HPoint HProfileAll]].
  apply (proj1 (source_sep_point_graph M (fun _=>body) 0 body point eq_refl)) in HPoint.
  destruct (code_relation_total M (E_separation_zero (CEvar 0)) (fun _=>p1))
    as [specialized HSpecialized].
  pose proof HSpecialized as HTarget.
  unfold E_separation_zero,E_sf_ex,E_sf_all in HTarget.
  destruct (schema_expression_quantifier_split M _ SFEx _ specialized HTarget)
    as [targetprofile [HTargetProfile HTargetEx]].
  destruct (schema_expression_quantifier_split M _ SFAll _ targetprofile HTargetProfile)
    as [targetpoint [HTargetPoint HTargetAll]].
  apply (proj1 (source_sep_point_graph M (fun _=>p1) 0 p1 targetpoint eq_refl)) in HTargetPoint.
  destruct (substitution_singleton_total M (zeroM M)) as [ub [uc [HU HTail]]].
  destruct (substitution_lift_total M ub uc (succM M (zeroM M)) (zeroM M)) as [d [e [j HL1]]].
  destruct (substitution_lift_total M d e j (succM M (zeroM M))) as [v [w [l HL2]]].
  pose proof (source_separation_body_zero_substitution M phi body p1 k ub uc d e j v w l
    HB HBody HP HU HL1 HL2) as HMatrix.
  destruct (source_separation_zero_map_atoms M ub uc d e j v w l HU HL1 HL2)
    as [H0 [H1 H2]].
  assert (HLeft:sf_relation M SFMember (code_numeral M 0) (code_numeral M 1) (source_sep_left_code M)).
  { exact (sf_make_numeral M SFMember 0 1). }
  assert (HRight:sf_relation M SFMember (code_numeral M 0) (code_numeral M 2) (source_sep_right_code M)).
  { exact (sf_make_numeral M SFMember 0 2). }
  assert (SLeft:numerical_substitution M (source_sep_left_code M) v w l
    (succM M (succM M (zeroM M))) (source_sep_left_code M)).
  { apply (proj2 (numerical_substitution_member M _ _ _ v w l _ _ HLeft)).
    exists (code_numeral M 0),(code_numeral M 1). repeat split;assumption. }
  assert (SRight:numerical_substitution M (source_sep_right_code M) v w l
    (succM M (succM M (zeroM M))) (source_sep_right_code M)).
  { apply (proj2 (numerical_substitution_member M _ _ _ v w l _ _ HRight)).
    exists (code_numeral M 0),(code_numeral M 2). repeat split;assumption. }
  assert (SPoint:numerical_substitution M point v w l
    (succM M (succM M (zeroM M))) targetpoint).
  { apply (source_prop_expression_substitution M
      (schema_env3 (source_sep_left_code M) (source_sep_right_code M) body)
      (schema_env3 (source_sep_left_code M) (source_sep_right_code M) p1)
      v w l (succM M (succM M (zeroM M))) separation_point_template
      ltac:(intros [|[|i]];cbn [schema_env3];assumption) point targetpoint HPoint HTargetPoint). }
  exists rawbody,specialized. split;[exact HRawAll|]. split;[|exact HSpecialized].
  exists ub,uc. split;[exact HU|].
  apply (proj2 (numerical_substitution_quantifier M false profile rawbody
    ub uc (succM M (zeroM M)) (zeroM M) specialized HRawEx)).
  exists d,e,j,targetprofile. split;[exact HL1|]. split;[|exact HTargetEx].
  apply (proj2 (numerical_substitution_quantifier M true point profile d e j
    (succM M (zeroM M)) targetprofile HProfileAll)).
  exists v,w,l,targetpoint. split;[exact HL2|]. split;assumption.
Qed.

Print Assumptions source_separation_zero_specialization.
