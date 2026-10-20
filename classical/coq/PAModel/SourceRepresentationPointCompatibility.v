(** Match the canonical representation points to the double-difference
    program by exact arithmetic-expression substitution. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions CodeExpressionPlug SetFormulaCodes
 SetSchemaConstructors SchemaConstructorBounds SourceRepresentationRecipe SourceRepresentationNamedPoint
 SourceRepresentationDifferenceProgram SourceRepresentationDifferencePoints SourcePropositionalTemplates.
Unset Implicit Arguments.
Lemma representation_named_point_plug M rho environment matrix name ev mv nv body :
 code_relation M rho environment ev ->code_relation M rho matrix mv ->code_relation M rho name nv ->
 (code_relation M rho(code_plug(schema_env3 environment matrix name)E_representation_named_point)body <->
  code_relation M(schema_env3 ev mv nv)E_representation_named_point body).
Proof. intros HE HM HN. apply code_relation_plug. intros[|[|i]];assumption. Qed.
Lemma representation_named_first_point M rho body :
 code_relation M rho(E_double_difference_all(SPTImpl(SPTSlot 6)(SPTIff(SPTSlot 0)(SPTSlot 4))))body <->
 code_relation M(schema_env3(rho 6)(rho 4)(succM M(rho 0)))E_representation_named_point body.
Proof.
 change(code_relation M rho(code_plug(schema_env3(CEvar 6)(CEvar 4)(CEadd(CEvar 0)(CEconst 1)))
   E_representation_named_point)body <->code_relation M(schema_env3(rho 6)(rho 4)(succM M(rho 0)))E_representation_named_point body).
 apply representation_named_point_plug;try reflexivity.
 exists(rho 0),(code_numeral M 1). split;[reflexivity|]. split;[reflexivity|apply Arithmetic.succ_as_add].
Qed.
Lemma representation_named_second_point M rho body :
 code_relation M rho(E_double_difference_all(SPTImpl(SPTSlot 6)(SPTIff(SPTSlot 1)(SPTSlot 5))))body <->
 code_relation M(schema_env3(rho 6)(rho 5)(succM M(rho 1)))E_representation_named_point body.
Proof.
 change(code_relation M rho(code_plug(schema_env3(CEvar 6)(CEvar 5)(CEadd(CEvar 1)(CEconst 1)))
   E_representation_named_point)body <->code_relation M(schema_env3(rho 6)(rho 5)(succM M(rho 1)))E_representation_named_point body).
 apply representation_named_point_plug;try reflexivity.
 exists(rho 1),(code_numeral M 1). split;[reflexivity|]. split;[reflexivity|apply Arithmetic.succ_as_add].
Qed.
Lemma representation_named_conjunction_point M rho conjunction body :
 sf_relation M SFAnd(rho 4)(rho 5) conjunction ->
 (code_relation M rho(E_double_difference_all double_difference_conclusion)body <->
 code_relation M(schema_env3(rho 6)conjunction(succM M(rho 3)))E_representation_named_point body).
Proof.
 intro HC. change(code_relation M rho(code_plug(schema_env3(CEvar 6)(E_sf SFAnd(CEvar 4)(CEvar 5))
    (CEadd(CEvar 3)(CEconst 1)))E_representation_named_point)body <->code_relation M(schema_env3(rho 6)conjunction(succM M(rho 3)))E_representation_named_point body).
 apply representation_named_point_plug;try reflexivity.
 - exact(proj2(schema_expression_graph M rho SFAnd(CEvar 4)(CEvar 5)(rho 4)(rho 5)conjunction eq_refl eq_refl) HC).
 - exists(rho 3),(code_numeral M 1). split;[reflexivity|]. split;[reflexivity|apply Arithmetic.succ_as_add].
Qed.
Print Assumptions representation_named_first_point.
Print Assumptions representation_named_second_point.
Print Assumptions representation_named_conjunction_point.
