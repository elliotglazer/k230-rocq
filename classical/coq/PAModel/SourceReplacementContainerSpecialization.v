(** Exact outer-All elimination in the literal Replacement range formula. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SetSchemaConstructors SchemaConstructorBounds SourceBounded SourceFiniteCutoffShift
  NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation
  SourceZFRReplacementUse SourcePropositionalTemplates SourcePropositionalSubstitution
  SourcePropositionalRebase SourceWFSeparationConstructor SourceSeparationContainerMaps
  SourceReplacementContainerMaps SchemaRenamingDescriptors.
Unset Implicit Arguments.

Definition E_replacement_container theta container:=E_sf_ex(E_sf_all
  (E_sf_iff(E_sf_mem 0 1)(E_sf_ex(E_sf SFAnd(E_sf SFMember(CEconst 0)container)theta)))).
Definition source_replacement_container_environment M A p2 i:=
  match i with 0=>p2|_=>source_succ_iter M 3 A end.
Definition replacement_container_iff_template:=
  SPTAnd(SPTImpl(SPTSlot 0)(SPTSlot 1))(SPTImpl(SPTSlot 1)(SPTSlot 0)).

Lemma source_replacement_container_iff_graph M env A B a b point:
  code_relation M env A a ->code_relation M env B b ->
  (code_relation M env(E_sf_iff A B)point <->
   code_relation M(schema_env3 a b(zeroM M))(source_prop_expression replacement_container_iff_template)point).
Proof.
  intros HA HB. apply(source_prop_expression_with_graph M env
    (fun i=>match i with 0=>A|1=>B|_=>CEconst 0 end)
    (schema_env3 a b(zeroM M))replacement_container_iff_template).
  intros[|[|i]];cbn[schema_env3];assumption||reflexivity.
Qed.

Theorem source_replacement_container_specialization M phi matrix range p2 k A:
  source_bounded M phi k ->schema_renaming M RepC phi matrix ->
  source_replacement_range_graph M matrix range ->source_cutoff_shift M 2 phi p2 ->
  exists rawbody specialized,
    sf_relation M SFAll rawbody(zeroM M)range /\numerical_instantiation M rawbody A specialized /\
    code_relation M(source_replacement_container_environment M A p2)
      (E_replacement_container(CEvar 0)(CEvar 1))specialized.
Proof.
  intros HB HMatrix HRange HP.
  unfold source_replacement_range_graph,E_source_replacement_range in HRange.
  destruct(schema_expression_quantifier_split M _ SFAll _ range HRange)as(rawbody&HRawBody&HRawAll).
  destruct(schema_expression_quantifier_split M _ SFEx _ rawbody HRawBody)as(profile&HProfile&HRawEx).
  destruct(schema_expression_quantifier_split M _ SFAll _ profile HProfile)as(point&HPoint&HProfileAll).
  destruct(code_relation_total M(E_sf_mem 0 1)(fun _=>matrix))as(left&HLeftCode).
  destruct(code_relation_total M(E_sf_ex(E_sf SFAnd(E_sf_mem 0 3)(CEvar 0)))(fun _=>matrix))as(ex&HExCode).
  apply(proj1(source_replacement_container_iff_graph M _ _ _ left ex point HLeftCode HExCode))in HPoint.
  destruct(schema_expression_quantifier_split M _ SFEx _ ex HExCode)as(body&HBody&HEx).
  destruct(schema_expression_split M _ SFAnd _ _ body HBody)as(input&cm&HInputCode&HCM&HAnd).
  change(cm=matrix)in HCM. subst cm.
  assert(HLeft:sf_relation M SFMember(zeroM M)(code_numeral M 1)left).
  { exact(proj1(schema_expression_graph M _ SFMember(CEconst 0)(CEconst 1)_ _ left eq_refl eq_refl)HLeftCode). }
  assert(HInput:sf_relation M SFMember(zeroM M)(code_numeral M 3)input).
  { exact(proj1(schema_expression_graph M _ SFMember(CEconst 0)(CEconst 3)_ _ input eq_refl eq_refl)HInputCode). }
  destruct(code_relation_total M(E_replacement_container(CEvar 0)(CEvar 1))
    (source_replacement_container_environment M A p2))as(specialized&HSpecialized).
  pose proof HSpecialized as HT. unfold E_replacement_container in HT.
  destruct(schema_expression_quantifier_split M _ SFEx _ specialized HT)as(tp&HTP&HTEx).
  destruct(schema_expression_quantifier_split M _ SFAll _ tp HTP)as(tpoint&HTPoint&HTAll).
  destruct(code_relation_total M(E_sf_mem 0 1)(source_replacement_container_environment M A p2))as(tleft&HTLeftCode).
  destruct(code_relation_total M(E_sf_ex(E_sf SFAnd(E_sf SFMember(CEconst 0)(CEvar 1))(CEvar 0)))
    (source_replacement_container_environment M A p2))as(tex&HTExCode).
  apply(proj1(source_replacement_container_iff_graph M _ _ _ tleft tex tpoint HTLeftCode HTExCode))in HTPoint.
  destruct(schema_expression_quantifier_split M _ SFEx _ tex HTExCode)as(tbody&HTBody&HTInnerEx).
  destruct(schema_expression_split M _ SFAnd _ _ tbody HTBody)as(tinput&tm&HTInputCode&HTM&HTAnd).
  change(tm=p2)in HTM. subst tm.
  assert(HTLeft:sf_relation M SFMember(zeroM M)(code_numeral M 1)tleft).
  { exact(proj1(schema_expression_graph M _ SFMember(CEconst 0)(CEconst 1)_ _ tleft eq_refl eq_refl)HTLeftCode). }
  assert(HTInput:sf_relation M SFMember(zeroM M)(source_succ_iter M 3 A)tinput).
  { exact(proj1(schema_expression_graph M _ SFMember(CEconst 0)(CEvar 1)_ _ tinput eq_refl eq_refl)HTInputCode). }
  destruct(substitution_singleton_total M A)as(ub&uc&HU&HTail).
  destruct(substitution_lift_total M ub uc(code_numeral M 1)(zeroM M))as(d&e&j&HL1).
  destruct(substitution_lift_total M d e j(code_numeral M 1))as(v&w&l&HL2).
  destruct(substitution_lift_total M v w l(code_numeral M 2))as(ab&ac&an&HL3).
  pose proof(source_replacement_body_container_substitution M phi matrix p2 k A ub uc d e j v w l ab ac an
    HB HMatrix HP HU HL1 HL2 HL3)as SMatrix.
  destruct(source_separation_container_map_atoms M A ub uc d e j v w l HU HL1 HL2)as(H0&H1&H2).
  destruct(source_replacement_container_map_atoms M A ub uc d e j v w l ab ac an HU HL1 HL2 HL3)as(HZ&HA).
  assert(SLeft:numerical_substitution M left v w l(code_numeral M 2)tleft).
  { apply(proj2(numerical_substitution_member M _ _ _ v w l _ _ HLeft)).
    exists(zeroM M),(code_numeral M 1). repeat split;assumption. }
  assert(SInput:numerical_substitution M input ab ac an(code_numeral M 3)tinput).
  { apply(proj2(numerical_substitution_member M _ _ _ ab ac an _ _ HInput)).
    exists(zeroM M),(source_succ_iter M 3 A). repeat split;assumption. }
  assert(SBody:numerical_substitution M body ab ac an(code_numeral M 3)tbody).
  { apply(proj2(numerical_substitution_binary M SFAnd input matrix body ab ac an _ tbody(or_introl eq_refl)HAnd)).
    exists tinput,p2. repeat split;assumption. }
  assert(SEx:numerical_substitution M ex v w l(code_numeral M 2)tex).
  { apply(proj2(numerical_substitution_quantifier M false body ex v w l(code_numeral M 2)tex HEx)).
    exists ab,ac,an,tbody. split;[exact HL3|]. split;[exact SBody|exact HTInnerEx]. }
  assert(SPoint:numerical_substitution M point v w l(code_numeral M 2)tpoint).
  { apply(source_prop_expression_substitution M(schema_env3 left ex(zeroM M))(schema_env3 tleft tex(zeroM M))
      v w l(code_numeral M 2)replacement_container_iff_template);[|exact HPoint|exact HTPoint].
    intros[|[|i]];cbn[schema_env3];try assumption.
    apply(proj2(numerical_substitution_invalid M(zeroM M)v w l(code_numeral M 2)(zeroM M)(or_introl eq_refl))). reflexivity. }
  exists rawbody,specialized. split;[exact HRawAll|]. split;[|exact HSpecialized].
  exists ub,uc. split;[exact HU|].
  apply(proj2(numerical_substitution_quantifier M false profile rawbody ub uc(code_numeral M 1)(zeroM M)specialized HRawEx)).
  exists d,e,j,tp. split;[exact HL1|]. split;[|exact HTEx].
  apply(proj2(numerical_substitution_quantifier M true point profile d e j(code_numeral M 1)tp HProfileAll)).
  exists v,w,l,tpoint. split;[exact HL2|]. split;[exact SPoint|exact HTAll].
Qed.
Print Assumptions source_replacement_container_iff_graph.
Print Assumptions source_replacement_container_specialization.
