(** Exact numerical shell of the fixed ordinal-element theorem, including
    actual Ord instantiation and the literal subset quantifier. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes
  SetSchemaConstructors SourcePropositionalRebase SourceFiniteParameters
  SourceFiniteParameterProofs SourceLeastOrdinalOld SourceLeastOrdinalFixed
  SourceOrdinalPredicate SourceOrdinalParameterCalibration SourceDomainInstances
  NumericalInstantiation SubstitutionSource.
Unset Implicit Arguments.

Definition ordinal_member_subset_expression := E_sf_all
  (E_sf SFImpl
    (E_sf SFMember (CEconst 0) (CEadd (CEconst 0) (CEconst 1)))
    (E_sf SFMember (CEconst 0) (CEadd (CEadd (CEvar 0) (CEconst 1)) (CEconst 1)))).
Definition ordinal_member_point_expression := E_sf SFImpl
  (E_sf SFMember (CEconst 0) (CEadd (CEvar 0) (CEconst 1)))
  (E_sf SFAnd
    (source_parameter_expression (source_parameter_up source_three_parameter_names) source_ordinal_predicate)
    ordinal_member_subset_expression).

Lemma ordinal_member_fixed_expression_shape :
  least_fixed_parameter_expression LeastOrdinalMember = E_sf SFImpl
    (source_parameter_expression source_three_parameter_names source_ordinal_predicate)
    (E_sf_all ordinal_member_point_expression).
Proof. reflexivity. Qed.

Lemma source_code_successor_graph M rho e x :code_relation M rho e x ->
  code_relation M rho (CEadd e (CEconst 1)) (succM M x).
Proof.
  intro HX. exists x,(code_numeral M 1). split;[exact HX|]. split;[reflexivity|].
  exact (Arithmetic.succ_as_add M x).
Qed.

Theorem source_ordinal_member_shell M rho law :
  code_relation M rho (least_fixed_parameter_expression LeastOrdinalMember) law ->
  exists ordA properties point member pair subset subsetpoint member01 memberA,
    numerical_instantiation M (source_ordinal_predicate_code M) (rho 0) ordA /\
    sf_relation M SFImpl ordA properties law /\
    sf_relation M SFAll point (zeroM M) properties /\
    sf_relation M SFMember (zeroM M) (succM M (rho 0)) member /\
    sf_relation M SFImpl member pair point /\
    sf_relation M SFAnd (source_ordinal_predicate_code M) subset pair /\
    sf_relation M SFAll subsetpoint (zeroM M) subset /\
    sf_relation M SFMember (zeroM M) (code_numeral M 1) member01 /\
    sf_relation M SFMember (zeroM M) (succM M (succM M (rho 0))) memberA /\
    sf_relation M SFImpl member01 memberA subsetpoint.
Proof.
  intro HG. rewrite ordinal_member_fixed_expression_shape in HG.
  destruct (schema_expression_split M rho SFImpl _ _ law HG)
    as (ordA&properties&HOrdA&HProperties&HLaw).
  destruct (schema_expression_split M rho SFAll _ (CEconst 0) properties HProperties)
    as (point&unused&HPoint&HUnused&HAll).
  destruct (schema_expression_split M rho SFImpl _ _ point HPoint)
    as (member&pair&HMember&HPair&HImp).
  destruct (schema_expression_split M rho SFAnd _ _ pair HPair)
    as (ordM&subset&HOrdM&HSubset&HPairGraph).
  destruct (schema_expression_split M rho SFAll _ (CEconst 0) subset HSubset)
    as (subsetpoint&unused'&HSubsetPoint&HUnused'&HSubsetAll).
  destruct (schema_expression_split M rho SFImpl _ _ subsetpoint HSubsetPoint)
    as (member01&memberA&HMember01&HMemberA&HSubsetImp).
  assert (HIA:numerical_instantiation M (source_ordinal_predicate_code M) (rho 0) ordA).
  { exact (source_parameter_ordinal_instance M source_three_parameter_names rho 0 (rho 0) ordA
      eq_refl HOrdA). }
  assert (HIM:numerical_instantiation M (source_ordinal_predicate_code M) (zeroM M) ordM).
  { exact (source_parameter_ordinal_instance M (source_parameter_up source_three_parameter_names)
      rho 0 (zeroM M) ordM eq_refl HOrdM). }
  pose proof (numerical_instantiation_functional M (source_ordinal_predicate_code M)
    (zeroM M) ordM (source_ordinal_predicate_code M) HIM
    (source_domain_instance_zero M _ (source_ordinal_predicate_bounded M))) as EM. subst ordM.
  assert (HMemberGraph:sf_relation M SFMember (zeroM M) (succM M (rho 0)) member).
  { exact (proj1 (substitution_source_constructor_graph M rho SFMember (CEconst 0) (CEadd (CEvar 0) (CEconst 1))
      (zeroM M) (succM M (rho 0)) member eq_refl
      (source_code_successor_graph M rho (CEvar 0) (rho 0) eq_refl)) HMember). }
  assert (HMember01Graph:sf_relation M SFMember (zeroM M) (code_numeral M 1) member01).
  { exact (proj1 (substitution_source_constructor_graph M rho SFMember (CEconst 0) (CEadd (CEconst 0) (CEconst 1))
      (zeroM M) (code_numeral M 1) member01 eq_refl
      (source_code_successor_graph M rho (CEconst 0) (zeroM M) eq_refl)) HMember01). }
  assert (HMemberAGraph:sf_relation M SFMember (zeroM M) (succM M (succM M (rho 0))) memberA).
  { exact (proj1 (substitution_source_constructor_graph M rho SFMember (CEconst 0) (CEadd (CEadd (CEvar 0) (CEconst 1)) (CEconst 1))
      (zeroM M) (succM M (succM M (rho 0))) memberA eq_refl
      (source_code_successor_graph M rho (CEadd (CEvar 0) (CEconst 1)) (succM M (rho 0))
        (source_code_successor_graph M rho (CEvar 0) (rho 0) eq_refl))) HMemberA). }
  exists ordA,properties,point,member,pair,subset,subsetpoint,member01,memberA.
  repeat split;assumption.
Qed.

Print Assumptions ordinal_member_fixed_expression_shape.
Print Assumptions source_code_successor_graph.
Print Assumptions source_ordinal_member_shell.

