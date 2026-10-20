(** Exact constructor graph of the pinned Foundation minimum lemma with
    arbitrary model-valued variable names. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes
  SetSchemaConstructors SourceFiniteParameters SourceFiniteParameterProofs SourceLeastOrdinalFixed
  SourcePropositionalRebase SourceWFSeparationConstructor SubstitutionSource.
Unset Implicit Arguments.

Definition regular_minimum_parameter_expression := E_sf SFImpl
  (E_sf SFMember (CEvar 1) (CEvar 0))
  (E_sf_ex (E_sf SFAnd
    (E_sf SFMember (CEconst 0) (CEadd (CEvar 0) (CEconst 1)))
    (E_sf_all (E_sf SFImpl (E_sf SFMember (CEconst 0) (CEadd (CEconst 0) (CEconst 1)))
      (E_sf SFImpl
        (E_sf SFMember (CEconst 0) (CEadd (CEadd (CEvar 0) (CEconst 1)) (CEconst 1)))
        (CEconst 0)))))).

Lemma regular_minimum_fixed_expression_shape :
  least_fixed_parameter_expression LeastRegularMinimum=regular_minimum_parameter_expression.
Proof. reflexivity. Qed.

Lemma source_code_expr_successor_graph M rho e x : code_relation M rho e x ->
  code_relation M rho (CEadd e (CEconst 1)) (succM M x).
Proof.
  intro HX. exists x,(code_numeral M 1). split;[exact HX|]. split;[reflexivity|].
  exact (Arithmetic.succ_as_add M x).
Qed.

Theorem source_regular_minimum_shell M rho law :
  code_relation M rho (least_fixed_parameter_expression LeastRegularMinimum) law ->
  exists premise minimum body member allexclusion exclusion member01 memberA neg,
    sf_relation M SFImpl premise minimum law /\
    sf_relation M SFMember (rho 1) (rho 0) premise /\
    sf_relation M SFEx body (zeroM M) minimum /\
    sf_relation M SFAnd member allexclusion body /\
    sf_relation M SFMember (zeroM M) (succM M (rho 0)) member /\
    sf_relation M SFAll exclusion (zeroM M) allexclusion /\
    sf_relation M SFImpl member01 neg exclusion /\
    sf_relation M SFMember (zeroM M) (code_numeral M 1) member01 /\
    sf_relation M SFImpl memberA (zeroM M) neg /\
    sf_relation M SFMember (zeroM M) (succM M (succM M (rho 0))) memberA.
Proof.
  intro HG. rewrite regular_minimum_fixed_expression_shape in HG.
  unfold regular_minimum_parameter_expression in HG.
  destruct (schema_expression_split M rho SFImpl _ _ law HG) as (premise&minimum&HP&HMin&HImpl).
  destruct (schema_expression_quantifier_split M rho SFEx _ minimum HMin) as (body&HB&HEx).
  destruct (schema_expression_split M rho SFAnd _ _ body HB) as (member&allexclusion&HM&HA&HAnd).
  destruct (schema_expression_quantifier_split M rho SFAll _ allexclusion HA) as (exclusion&HE&HAll).
  destruct (schema_expression_split M rho SFImpl _ _ exclusion HE) as (member01&neg&HM01&HN&HExc).
  destruct (schema_expression_split M rho SFImpl _ _ neg HN) as (memberA&f&HMA&HF&HNeg).
  change (f=zeroM M) in HF. subst f.
  assert (HPre:sf_relation M SFMember (rho 1) (rho 0) premise).
  { exact (proj1 (substitution_source_constructor_graph M rho SFMember (CEvar 1) (CEvar 0)
      (rho 1) (rho 0) premise eq_refl eq_refl) HP). }
  assert (HMember:sf_relation M SFMember (zeroM M) (succM M (rho 0)) member).
  { exact (proj1 (substitution_source_constructor_graph M rho SFMember (CEconst 0)
      (CEadd (CEvar 0) (CEconst 1)) (zeroM M) (succM M (rho 0)) member eq_refl
      (source_code_expr_successor_graph M rho (CEvar 0) (rho 0) eq_refl)) HM). }
  assert (HMember01:sf_relation M SFMember (zeroM M) (code_numeral M 1) member01).
  { exact (proj1 (substitution_source_constructor_graph M rho SFMember (CEconst 0) (CEadd (CEconst 0) (CEconst 1))
      (zeroM M) (code_numeral M 1) member01 eq_refl
      (source_code_expr_successor_graph M rho (CEconst 0) (zeroM M) eq_refl)) HM01). }
  assert (HMemberA:sf_relation M SFMember (zeroM M) (succM M (succM M (rho 0))) memberA).
  { exact (proj1 (substitution_source_constructor_graph M rho SFMember (CEconst 0)
      (CEadd (CEadd (CEvar 0) (CEconst 1)) (CEconst 1))
      (zeroM M) (succM M (succM M (rho 0))) memberA eq_refl
      (source_code_expr_successor_graph M rho (CEadd (CEvar 0) (CEconst 1)) (succM M (rho 0))
        (source_code_expr_successor_graph M rho (CEvar 0) (rho 0) eq_refl))) HMA). }
  exists premise,minimum,body,member,allexclusion,exclusion,member01,memberA,neg.
  repeat split;assumption.
Qed.

Print Assumptions regular_minimum_fixed_expression_shape.
Print Assumptions source_regular_minimum_shell.
