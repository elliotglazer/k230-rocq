(** Exact constructor graph of the pinned ordinal-successor container law. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SetSchemaConstructors
  SourceFiniteParameters SourceFiniteParameterProofs SourceLeastOrdinalFixed
  SourceOrdinalPredicate SourceOrdinalParameterCalibration SourceDomainInstances NumericalInstantiation
  SourcePropositionalRebase SourceWFSeparationConstructor SourceRegularMinimumShell SubstitutionSource.
Unset Implicit Arguments.

Definition successor_container_parameter_expression := E_sf SFImpl
  (source_parameter_expression source_three_parameter_names source_ordinal_predicate)
  (E_sf_ex (E_sf SFAnd
    (source_parameter_expression (source_parameter_up source_three_parameter_names) source_ordinal_predicate)
    (E_sf SFMember (CEadd (CEvar 0) (CEconst 1)) (CEconst 0)))).

Lemma successor_container_fixed_expression_shape :
  least_fixed_parameter_expression LeastSuccessorContainer=successor_container_parameter_expression.
Proof. reflexivity. Qed.

Theorem source_successor_container_shell M rho law :
  code_relation M rho (least_fixed_parameter_expression LeastSuccessorContainer) law ->
  exists ordA container body member,
    numerical_instantiation M (source_ordinal_predicate_code M) (rho 0) ordA /\
    sf_relation M SFImpl ordA container law /\
    sf_relation M SFEx body (zeroM M) container /\
    sf_relation M SFAnd (source_ordinal_predicate_code M) member body /\
    sf_relation M SFMember (succM M (rho 0)) (zeroM M) member.
Proof.
  intro HG. rewrite successor_container_fixed_expression_shape in HG.
  unfold successor_container_parameter_expression in HG.
  destruct (schema_expression_split M rho SFImpl _ _ law HG) as (ordA&container&HOrdA&HContainer&HImpl).
  destruct (schema_expression_quantifier_split M rho SFEx _ container HContainer) as (body&HBody&HEx).
  destruct (schema_expression_split M rho SFAnd _ _ body HBody) as (ordC&member&HOrdC&HMember&HAnd).
  assert (HIA:numerical_instantiation M (source_ordinal_predicate_code M) (rho 0) ordA).
  { exact (source_parameter_ordinal_instance M source_three_parameter_names rho 0 (rho 0) ordA
      eq_refl HOrdA). }
  assert (HIC:numerical_instantiation M (source_ordinal_predicate_code M) (zeroM M) ordC).
  { exact (source_parameter_ordinal_instance M (source_parameter_up source_three_parameter_names)
      rho 0 (zeroM M) ordC eq_refl HOrdC). }
  pose proof (numerical_instantiation_functional M (source_ordinal_predicate_code M) (zeroM M)
    ordC (source_ordinal_predicate_code M) HIC
    (source_domain_instance_zero M _ (source_ordinal_predicate_bounded M))) as EOrd. subst ordC.
  assert (HM:sf_relation M SFMember (succM M (rho 0)) (zeroM M) member).
  { exact (proj1 (substitution_source_constructor_graph M rho SFMember
      (CEadd (CEvar 0) (CEconst 1)) (CEconst 0) (succM M (rho 0)) (zeroM M) member
      (source_code_expr_successor_graph M rho (CEvar 0) (rho 0) eq_refl) eq_refl) HMember). }
  exists ordA,container,body,member. repeat split;assumption.
Qed.

Print Assumptions successor_container_fixed_expression_shape.
Print Assumptions source_successor_container_shell.
