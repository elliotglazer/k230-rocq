(** Actual Separation specialization at any model-valued container name. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SetSchemaConstructors SchemaConstructorBounds SourceBounded SourceFiniteCutoffShift SchemaRenamingDescriptors
  NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation SourceNumeralLift
  SourcePropositionalTemplates SourceSeparationSubset SourceWFSeparationWitness
  SourceWFSeparationConstructor SourcePropositionalSubstitution SourceSeparationSpecializationMaps SourceSeparationContainerMaps SourcePropositionalRebase.
Unset Implicit Arguments.

Definition E_separation_container theta container:=
 E_sf_ex(E_sf_all(E_sf_iff(E_sf_mem 0 1)
  (E_sf SFAnd(E_sf SFMember(CEconst 0)container)theta))).
Definition source_separation_container_environment M A p1 i:=match i with 0=>p1|_=>succM M(succM M A)end.
Lemma source_sep_container_point_graph M A p1 right point:
 sf_relation M SFMember(zeroM M)(succM M(succM M A))right ->
 (code_relation M(source_separation_container_environment M A p1)
  (E_sf_iff(E_sf_mem 0 1)(E_sf SFAnd(E_sf SFMember(CEconst 0)(CEvar 1))(CEvar 0)))point <->
 code_relation M(schema_env3(source_sep_left_code M)right p1)(source_prop_expression separation_point_template)point).
Proof.
 intro HR. apply(source_prop_expression_with_graph M(source_separation_container_environment M A p1)
  (fun i=>match i with 0=>E_sf_mem 0 1|1=>E_sf SFMember(CEconst 0)(CEvar 1)|_=>CEvar 0 end)
  (schema_env3(source_sep_left_code M)right p1)separation_point_template).
 intros[|[|i]];cbn[schema_env3].
 - apply(proj2(schema_expression_graph M _ SFMember(CEconst 0)(CEconst 1)
   (zeroM M)(code_numeral M 1)(source_sep_left_code M)eq_refl eq_refl)). exact(sf_make_numeral M SFMember 0 1).
 - exact(proj2(schema_expression_graph M _ SFMember(CEconst 0)(CEvar 1)
   (zeroM M)(succM M(succM M A))right eq_refl eq_refl)HR).
 - reflexivity.
Qed.
Local Opaque source_sep_left_code source_sep_right_code.
Theorem source_separation_container_specialization M phi body raw p1 k A :
  source_bounded M phi k ->
  schema_renaming M SepBody phi body ->
  sf_separation_constructor M body raw ->
  source_cutoff_shift M 1 phi p1 ->
  exists rawbody specialized,
    sf_relation M SFAll rawbody (zeroM M) raw /\
    numerical_instantiation M rawbody A specialized /\
    code_relation M(source_separation_container_environment M A p1)(E_separation_container(CEvar 0)(CEvar 1))specialized.
Proof.
  intros HB HBody HRaw HP.
  destruct(sf_relation_total M SFMember(zeroM M)(succM M(succM M A)))as(right&HRightA).
  unfold sf_separation_constructor,E_sf_separation,E_sf_all,E_sf_ex in HRaw.
  destruct (schema_expression_quantifier_split M _ SFAll _ raw HRaw)
    as [rawbody [HRawBody HRawAll]].
  destruct (schema_expression_quantifier_split M _ SFEx _ rawbody HRawBody)
    as [profile [HProfile HRawEx]].
  destruct (schema_expression_quantifier_split M _ SFAll _ profile HProfile)
    as [point [HPoint HProfileAll]].
  apply (proj1 (source_sep_point_graph M (fun _=>body) 0 body point eq_refl)) in HPoint.
  destruct (code_relation_total M (E_separation_container(CEvar 0)(CEvar 1))(source_separation_container_environment M A p1))
    as [specialized HSpecialized].
  pose proof HSpecialized as HTarget.
  unfold E_separation_container,E_sf_ex,E_sf_all in HTarget.
  destruct (schema_expression_quantifier_split M _ SFEx _ specialized HTarget)
    as [targetprofile [HTargetProfile HTargetEx]].
  destruct (schema_expression_quantifier_split M _ SFAll _ targetprofile HTargetProfile)
    as [targetpoint [HTargetPoint HTargetAll]].
  apply (proj1 (source_sep_container_point_graph M A p1 right targetpoint HRightA)) in HTargetPoint.
  destruct (substitution_singleton_total M A) as [ub [uc [HU HTail]]].
  destruct (substitution_lift_total M ub uc (succM M (zeroM M)) (zeroM M)) as [d [e [j HL1]]].
  destruct (substitution_lift_total M d e j (succM M (zeroM M))) as [v [w [l HL2]]].
  pose proof (source_separation_body_container_substitution M phi body p1 k A ub uc d e j v w l
    HB HBody HP HU HL1 HL2) as HMatrix.
  destruct (source_separation_container_map_atoms M A ub uc d e j v w l HU HL1 HL2)
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
    (succM M (succM M (zeroM M))) right).
  { apply (proj2 (numerical_substitution_member M _ _ _ v w l _ _ HRight)).
    exists(zeroM M),(succM M(succM M A)). repeat split;assumption. }
  assert (SPoint:numerical_substitution M point v w l
    (succM M (succM M (zeroM M))) targetpoint).
  { apply (source_prop_expression_substitution M
      (schema_env3 (source_sep_left_code M) (source_sep_right_code M) body)
      (schema_env3 (source_sep_left_code M) right p1)
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


Print Assumptions source_sep_container_point_graph.
Print Assumptions source_separation_container_specialization.
