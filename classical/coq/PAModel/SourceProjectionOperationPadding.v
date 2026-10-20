(** Literal projection parameters pad above any internal assignment count.
    Applies to Op4 and any fixed four-parameter source bounded by4. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes SourceFiniteParameters
 SourceFiniteNameParameters SourceParameterRenamingTransport SourceRepresentationPadding NumericalRenaming FixedSourceBounds.
From Undecidability.FOL Require Import Syntax.Bounded.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Definition projection_outer_roles M i:=match i with
 |0=>code_numeral M 2|1=>code_numeral M 3|2=>code_numeral M 1|_=>zeroM M end.
Definition projection_inner_roles M count i:=match i with
 |0=>addM M count(code_numeral M 2)|1=>addM M count(code_numeral M 3)|2=>code_numeral M 1|_=>zeroM M end.
Theorem source_projection_operation_padding M count(phi:sf_form)op padded:
 bounded 4 phi ->
 code_relation M(projection_outer_roles M)(source_parameter_expression(source_finite_parameter_names 4)phi)op ->
 code_relation M(projection_inner_roles M count)(source_parameter_expression(source_finite_parameter_names 4)phi)padded ->
 source_representation_padding M count op padded.
Proof.
 intros HB HO HP.
 apply(source_parameter_renaming_transport M 4 phi HB(source_finite_parameter_names 4)(source_finite_parameter_names 4)
  (projection_outer_roles M)(projection_inner_roles M count)(code_numeral M 6)(code_numeral M 2)(code_numeral M 2)count op padded);
  [|exact HO|exact HP].
 intros[|[|[|[|i]]]]x y HI HX HY;try lia.
 - change(x=code_numeral M 2)in HX. change(y=addM M count(code_numeral M 2))in HY. subst x y.
   rewrite Arithmetic.add_comm. apply representation_padding_outside_lookup.
   intro H. apply(proj1(fixed_source_numeral_lt_iff M 2 2))in H. lia.
 - change(x=code_numeral M 3)in HX. change(y=addM M count(code_numeral M 3))in HY. subst x y.
   rewrite Arithmetic.add_comm. apply representation_padding_outside_lookup.
   intro H. apply(proj1(fixed_source_numeral_lt_iff M 3 2))in H. lia.
 - change(x=code_numeral M 1)in HX. change(y=code_numeral M 1)in HY. subst x y.
   apply representation_padding_one_lookup.
 - change(x=zeroM M)in HX. change(y=zeroM M)in HY. subst x y.
   apply representation_padding_zero_lookup.
Qed.
Print Assumptions source_projection_operation_padding.
