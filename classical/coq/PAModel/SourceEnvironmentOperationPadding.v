(** The exact Op3(An,A,A,Next) condition under Dn padding. Only the
    auxiliary old-carrier name moves; the new carrier and A stay at0/1. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 SourceEnvironmentPointSlots SourceFiniteParameters SourceFiniteNameParameters SourceFiniteParameterProofs SourceParameterGraphs
 SourceThreeParameterCommutation SourceRepresentationPadding NumericalRenaming SourceNumeralLift FixedSourceBounds.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Definition environment_operation_roles(M:Model)(oldr:carrier M)i:=match i with
 |0=>oldr|1=>code_numeral M 1|_=>zeroM M end.
Definition source_environment_operation_graph M oldr op:=code_relation M(environment_operation_roles M oldr)
 (source_parameter_expression source_three_parameter_names environment_operation_source)op.
Theorem source_environment_operation_fixed_graph M rho op:
 rho 1=code_numeral M 1 ->rho 2=zeroM M ->
 (code_relation M rho(environment_extension_fixed_slot 0)op <->source_environment_operation_graph M(rho 0)op).
Proof.
 intros H1 H2. unfold source_environment_operation_graph,environment_extension_fixed_slot.
 apply(source_parameter_graph_ext M 3 environment_operation_source environment_operation_source_bound
  (source_finite_parameter_names 6)source_three_parameter_names rho(environment_operation_roles M(rho 0))).
 intros[|[|[|i]]]v HI;try lia.
 - reflexivity.
 - change(v=rho 1 <->v=code_numeral M 1). now rewrite H1.
 - change(v=rho 2 <->v=zeroM M). now rewrite H2.
Qed.
Theorem source_environment_operation_padding M count op padded:
 source_environment_operation_graph M(code_numeral M 2)op ->
 source_environment_operation_graph M(succM M(succM M count))padded ->source_representation_padding M count op padded.
Proof.
 intros HO HP. apply(source_three_parameter_renaming_commutation M environment_operation_source
  (environment_operation_roles M(code_numeral M 2))(environment_operation_roles M(succM M(succM M count)))op padded
  (code_numeral M 6)(code_numeral M 2)(code_numeral M 2)count environment_operation_source_bound HO HP).
 intros[|[|[|i]]]HI;cbn[environment_operation_roles];try lia.
 - pose proof(representation_padding_outside_lookup M count(code_numeral M 2)
   ltac:(intro H;apply(proj1(fixed_source_numeral_lt_iff M 2 2))in H;lia))as H.
   change(representation_padding_lookup M count(code_numeral M 2)
    (addM M(succM M(succM M(zeroM M)))count))in H.
   now rewrite!Arithmetic.add_succ,Arithmetic.add_zero in H.
 - apply representation_padding_one_lookup.
 - apply representation_padding_zero_lookup.
Qed.
Theorem source_environment_operation_graph_bound M oldr op k:
 coding_lt M oldr k ->coding_lt M(code_numeral M 1)k ->coding_lt M(zeroM M)k ->
 source_environment_operation_graph M oldr op ->source_bounded M op k.
Proof.
 intros HO H1 H0 HG. apply(source_parameter_graph_bounded M 3 environment_operation_source environment_operation_source_bound
  source_three_parameter_names(environment_operation_roles M oldr)k);[|exact HG].
 intros[|[|[|i]]]v HI HV;try lia.
 - change(v=oldr)in HV. now subst v.
 - change(v=code_numeral M 1)in HV. now subst v.
 - change(v=zeroM M)in HV. now subst v.
Qed.
Print Assumptions source_environment_operation_fixed_graph.
Print Assumptions source_environment_operation_padding.
Print Assumptions source_environment_operation_graph_bound.

