(** Match the literal disjunction representation point to pair/union. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions CodeExpressionPlug SetFormulaCodes
 SetSchemaConstructors SchemaConstructorBounds SourceRepresentationNamedPoint SourceRepresentationPointCompatibility
 SourceRepresentationDifferencePoints SourcePairUnionProgram.
Unset Implicit Arguments.
Lemma representation_named_disjunction_point M rho disjunction body:
 sf_relation M SFOr(rho 4)(rho 5)disjunction ->
 (code_relation M rho(E_double_difference_all pair_union_conclusion)body <->
 code_relation M(schema_env3(rho 6)disjunction(succM M(rho 3)))E_representation_named_point body).
Proof.
 intro HC. change(code_relation M rho(code_plug(schema_env3(CEvar 6)(E_sf SFOr(CEvar 4)(CEvar 5))
  (CEadd(CEvar 3)(CEconst 1)))E_representation_named_point)body <->
  code_relation M(schema_env3(rho 6)disjunction(succM M(rho 3)))E_representation_named_point body).
 apply representation_named_point_plug;try reflexivity.
 - exact(proj2(schema_expression_graph M rho SFOr(CEvar 4)(CEvar 5)(rho 4)(rho 5)disjunction eq_refl eq_refl)HC).
 - exists(rho 3),(code_numeral M 1). split;[reflexivity|]. split;[reflexivity|apply Arithmetic.succ_as_add].
Qed.
Print Assumptions representation_named_disjunction_point.
