(** Actual fresh-name existential binders in the literal finite PJ profile. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SetSchemaConstructors
 SourceProjectionFiniteSyntax SourceFiniteParameterNamedBinder SourceFiniteParameters SourceFiniteNameParameters
 SourceFiniteParameterProofs SourceParameterGraphs SourceFiniteParameterComposition SourceDefinabilityPrimitives
 SourceEnvironmentExtensionScopes SourceEnvironmentCarrierClosure SourceNamedQuantifierRules.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
From Stdlib Require Import Lia.
Open Scope minZFsyn.
Unset Implicit Arguments.
Definition projection_extension_sigma i:sf_term:=match i with 0=>$3|1=>$0|_=>$1 end.
Lemma projection_inner_body_literal:projection_inner_body4=
 (($0 ∈' $2)∧source_def_extension021[projection_extension_sigma]).
Proof. reflexivity. Qed.
Definition projection_three_values {A}(a b c:A)i:=match i with 0=>a|1=>b|_=>c end.
Theorem source_projection_inner_body_graph M a child p e extension member body:
 code_relation M(environment_extension_names M p e a)
  (source_parameter_expression source_three_parameter_names source_def_extension021)extension ->
 sf_relation M SFMember e child member ->sf_relation M SFAnd member extension body ->
 code_relation M(finite_binder_environment e(projection_three_values a child p))
  (source_parameter_expression(source_finite_parameter_names 4)projection_inner_body4)body.
Proof.
 intros HExt HMember HBody. rewrite projection_inner_body_literal.
 cbn[source_parameter_expression]. rewrite source_parameter_substitution.
 assert(HX:code_relation M(finite_binder_environment e(projection_three_values a child p))
  (source_parameter_expression(fun i=>source_finite_parameter_names 4(sf_index(projection_extension_sigma i)))source_def_extension021)extension).
 { apply(proj2(source_parameter_graph_ext M 3 source_def_extension021 source_def_extension_bound
    (fun i=>source_finite_parameter_names 4(sf_index(projection_extension_sigma i)))source_three_parameter_names
    (finite_binder_environment e(projection_three_values a child p))(environment_extension_names M p e a)
    ltac:(intros[|[|[|i]]]v HI;try lia;reflexivity)extension)). exact HExt. }
 eapply environment_carrier_code_join;[|exact HX|exact HBody].
 eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HMember].
Qed.
Theorem source_projection_inner_named_exists M a child p e extension member body inner:
 e<>a ->e<>child ->e<>p ->
 code_relation M(environment_extension_names M p e a)
  (source_parameter_expression source_three_parameter_names source_def_extension021)extension ->
 sf_relation M SFMember e child member ->sf_relation M SFAnd member extension body ->
 code_relation M(projection_three_values a child p)
  (source_parameter_expression(source_finite_parameter_names 3)projection_inner3)inner ->
 source_named_quantifier M false e body inner.
Proof.
 intros EA EC EP HExt HM HB HI.
 apply(source_finite_parameter_named_binder M 3 projection_inner_body4(projection_three_values a child p)e body inner false).
 - exact projection_inner_body_bound.
 - intros[|[|[|i]]]HN;try lia;assumption.
 - exact(source_projection_inner_body_graph M a child p e extension member body HExt HM HB).
 - exact HI.
Qed.
Print Assumptions projection_inner_body_literal.
Print Assumptions source_projection_inner_named_exists.

Definition projection_inner_sigma i:sf_term:=match i with 0=>$0|1=>$1|_=>$3 end.
Lemma projection_outer_body_literal:projection_outer_body4=
 (($0 ∈' $2)∧projection_inner3[projection_inner_sigma]).
Proof. reflexivity. Qed.
Theorem source_projection_outer_body_graph M child A p a inner member body:
 code_relation M(projection_three_values a child p)
  (source_parameter_expression(source_finite_parameter_names 3)projection_inner3)inner ->
 sf_relation M SFMember a A member ->sf_relation M SFAnd member inner body ->
 code_relation M(finite_binder_environment a(projection_three_values child A p))
  (source_parameter_expression(source_finite_parameter_names 4)projection_outer_body4)body.
Proof.
 intros HInner HMember HBody. rewrite projection_outer_body_literal.
 cbn[source_parameter_expression]. rewrite source_parameter_substitution.
 assert(HX:code_relation M(finite_binder_environment a(projection_three_values child A p))
  (source_parameter_expression(fun i=>source_finite_parameter_names 4(sf_index(projection_inner_sigma i)))projection_inner3)inner).
 { apply(proj2(source_parameter_graph_ext M 3 projection_inner3 projection_inner_bound
    (fun i=>source_finite_parameter_names 4(sf_index(projection_inner_sigma i)))(source_finite_parameter_names 3)
    (finite_binder_environment a(projection_three_values child A p))(projection_three_values a child p)
    ltac:(intros[|[|[|i]]]v HI;try lia;reflexivity)inner)). exact HInner. }
 eapply environment_carrier_code_join;[|exact HX|exact HBody].
 eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HMember].
Qed.
Theorem source_projection_outer_named_exists M child A p a inner member body profile:
 a<>child ->a<>A ->a<>p ->
 code_relation M(projection_three_values a child p)
  (source_parameter_expression(source_finite_parameter_names 3)projection_inner3)inner ->
 sf_relation M SFMember a A member ->sf_relation M SFAnd member inner body ->
 code_relation M(projection_three_values child A p)
  (source_parameter_expression(source_finite_parameter_names 3)projection_PJ3)profile ->
 source_named_quantifier M false a body profile.
Proof.
 intros AC AA AP HInner HM HB HP.
 apply(source_finite_parameter_named_binder M 3 projection_outer_body4(projection_three_values child A p)a body profile false).
 - exact projection_outer_body_bound.
 - intros[|[|[|i]]]HN;try lia;assumption.
 - exact(source_projection_outer_body_graph M child A p a inner member body HInner HM HB).
 - exact HP.
Qed.
Print Assumptions projection_outer_body_literal.
Print Assumptions source_projection_outer_named_exists.
