(** Exact free-name bounds for all implication difference point shells. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SourceBounded SchemaConstructorBounds SourcePropositionalTemplates
 SourceRepresentationPointBounds SourceImplicationDifferenceUniversal SourceRepresentationDifferencePoints.
Unset Implicit Arguments.
Theorem implication_difference_all_expression_bound M rho k p:
 (forall i,(i<4)%nat->coding_lt M(rho i)k)->coding_lt M(rho 7)k->
 source_bounded M(rho 4)(succM M k)->source_bounded M(rho 5)(succM M k)->source_bounded M(rho 6)(succM M k)->
 schema_expression_bound M rho(E_implication_difference_all p)k.
Proof.
 intros HNames HCarrier B4 B5 B6. apply schema_expression_unary;[left;reflexivity|].
 apply source_prop_plug_expression_bound. intros[|[|[|[|[|[|[|i]]]]]]];cbn[implication_difference_point_plug].
 - apply representation_member_expression_bound,HNames. auto.
 - apply representation_member_expression_bound,HNames. auto.
 - apply representation_member_expression_bound,HNames. auto.
 - apply representation_member_expression_bound,HNames. auto.
 - apply schema_expression_variable. exact B4.
 - apply schema_expression_variable. exact B5.
 - apply schema_expression_variable. exact B6.
 - apply representation_member_expression_bound. exact HCarrier.
Qed.
Print Assumptions implication_difference_all_expression_bound.
