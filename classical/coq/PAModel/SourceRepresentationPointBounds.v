(** Free-variable bounds for the actual double-difference point syntax. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions CodeExpressionPlug
 SetFormulaCodes SchemaConstructorBounds SourceBounded SourcePropositionalTemplates
 SourceRepresentationDifferencePoints.
Unset Implicit Arguments.
Lemma code_plug_source_constructor sigma h a b :code_plug sigma(E_sf h a b)=E_sf h(code_plug sigma a)(code_plug sigma b).
Proof. destruct h;reflexivity. Qed.
Lemma source_prop_plug_expression_bound M rho sigma p k :
 (forall i,schema_expression_bound M rho(sigma i)k) ->
 schema_expression_bound M rho(code_plug sigma(source_prop_expression p))k.
Proof.
 intro HH. induction p;cbn[code_plug source_prop_expression].
 - apply HH.
 - intros f HF. change(f=zeroM M)in HF. subst f. apply source_bounded_accept_falsity.
 - rewrite code_plug_source_constructor. apply schema_expression_binary;[right;right;reflexivity|exact IHp1|exact IHp2].
 - rewrite code_plug_source_constructor. apply schema_expression_binary;[left;reflexivity|exact IHp1|exact IHp2].
 - rewrite code_plug_source_constructor. apply schema_expression_binary;[right;left;reflexivity|exact IHp1|exact IHp2].
Qed.
Lemma representation_member_expression_bound M rho i k :coding_lt M(rho i)k ->
 schema_expression_bound M rho(representation_member_expression(CEvar i))(succM M k).
Proof.
 intros HI f HF.
 assert(HIndex:code_relation M rho(CEadd(CEvar i)(CEconst 1))(succM M(rho i))).
 { exists(rho i),(code_numeral M 1). split;[reflexivity|]. split;[reflexivity|apply Arithmetic.succ_as_add]. }
 apply(proj2(source_bounded_accept_atom M SFMember(zeroM M)(succM M(rho i))f(succM M k)
  (or_introl eq_refl)(proj1(schema_expression_graph M rho SFMember(CEconst 0)(CEadd(CEvar i)(CEconst 1))
    (zeroM M)(succM M(rho i))f eq_refl HIndex) HF))).
 split;[apply coding_zero_lt_succ|apply coding_lt_succ_cancel;exact HI].
Qed.
Theorem double_difference_all_expression_bound M rho k p :
 (forall i,(i<4)%nat ->coding_lt M(rho i)k) ->
 source_bounded M(rho 4)(succM M k) ->source_bounded M(rho 5)(succM M k) ->
 source_bounded M(rho 6)(succM M k) ->schema_expression_bound M rho(E_double_difference_all p)k.
Proof.
 intros HNames B4 B5 B6. apply schema_expression_unary;[left;reflexivity|].
 apply source_prop_plug_expression_bound. intros[|[|[|[|[|[|i]]]]]];cbn[double_difference_point_plug].
 - apply representation_member_expression_bound,HNames. auto.
 - apply representation_member_expression_bound,HNames. auto.
 - apply representation_member_expression_bound,HNames. auto.
 - apply representation_member_expression_bound,HNames. auto.
 - apply schema_expression_variable. exact B4.
 - apply schema_expression_variable. exact B5.
 - apply schema_expression_variable. exact B6.
Qed.
Print Assumptions double_difference_all_expression_bound.

