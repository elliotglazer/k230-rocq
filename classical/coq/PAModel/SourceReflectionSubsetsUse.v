(** Actual AllE/MP use of the exact fixed union-family subset predicate. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SourceReflectionGeometryPredicates SourceReflectionUnionOld SourceRecursionPrimitiveRelations
  SourceFiniteParameters SourceFiniteNameParameters SourceSubsetParameterCalibration SourceRawSubset
  SourceSubsetSubstitution SourcePropositionalRebase SourceTracePointRules SourceInstantiationConstructors
  NumericalSubstitutionMaps NumericalSubstitution SubstitutionSource NumericalInstantiation NumericalSourceFull SourceDerivedRules
  OldNamedSyntaxBridge SchemaConstructorBounds.
Unset Implicit Arguments.

Theorem source_full_reflection_subsets_use M K beta w whole member subset gb gc gn:
  source_reflection_geometry_instance M ReflectionSubsets(source_rec_env2 K beta)whole ->
  sf_relation M SFMember w K member ->source_raw_subset_graph M w beta subset ->
  source_full_prv M gb gc gn whole ->source_full_prv M gb gc gn member ->
  source_full_prv M gb gc gn subset.
Proof.
  intros HWhole HMember HSubset PWhole PMember.
  set(rho:=source_rec_env2 K beta).
  set(names:=source_finite_parameter_names 2).
  change(code_relation M rho
    (E_sf SFAll(E_sf SFImpl(E_sf SFMember(CEconst 0)(CEadd(names 0)(CEconst 1)))
      (source_parameter_expression(source_parameter_up names)
        (isolated_formula(OldZFC.Z_base.Sub0(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 2)))))
      (CEconst 0))whole)in HWhole.
  destruct(schema_expression_split M rho SFAll _ _ whole HWhole)as(point&z&HPoint&HZ&HAll).
  change(z=zeroM M)in HZ. subst z.
  destruct(schema_expression_split M rho SFImpl _ _ point HPoint)as(guard&raw&HGuard&HRaw&HImpl).
  assert(NS:code_relation M rho(CEadd(names 0)(CEconst 1))(succM M K)).
  { exists K,(code_numeral M 1). split;[reflexivity|]. split;[reflexivity|exact(Arithmetic.succ_as_add M K)]. }
  assert(HG:sf_relation M SFMember(zeroM M)(succM M K)guard).
  { exact(proj1(schema_expression_graph M rho SFMember(CEconst 0)_ (zeroM M)(succM M K)guard eq_refl NS)HGuard). }
  assert(U0:code_relation M rho(source_parameter_up names 0)(zeroM M))by reflexivity.
  assert(U2:code_relation M rho(source_parameter_up names 2)(succM M beta)).
  { exists beta,(code_numeral M 1). split;[reflexivity|]. split;[reflexivity|exact(Arithmetic.succ_as_add M beta)]. }
  pose proof(source_parameter_raw_subset M(source_parameter_up names)rho 0 2(zeroM M)(succM M beta)raw U0 U2 HRaw)as HR.
  destruct(substitution_singleton_total M w)as(ib&ic&HHead&_).
  assert(HIR:numerical_instantiation M raw w subset).
  { exists ib,ic. split;[exact HHead|].
    exact(source_oc_subset_substitution M(zeroM M)(succM M beta)raw w beta subset
      ib ic(code_numeral M 1)(zeroM M)HR HHead(substitution_singleton_tail M ib ic beta)HSubset). }
  pose proof(source_instantiation_head_member M K guard w member HG HMember)as HIG.
  destruct(sf_relation_total M SFImpl member subset)as(instance&HInstance).
  pose proof(source_instantiation_binary M SFImpl guard raw point w member subset instance
    (or_intror(or_intror eq_refl))HImpl HIG HIR HInstance)as HI.
  pose proof(full_source_AllE M gb gc gn point whole w instance
    (source_wf_quantifier_instance M gb gc gn SFAll point whole w instance(or_introl eq_refl)
      HAll(source_full_prv_wellformed M gb gc gn whole PWhole)HI)PWhole HAll HI)as PInstance.
  exact(source_full_modus_ponens M gb gc gn member subset instance HInstance PInstance PMember).
Qed.

Print Assumptions source_full_reflection_subsets_use.
