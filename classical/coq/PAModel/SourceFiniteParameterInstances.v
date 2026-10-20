(** Literal instantiation of a fixed finite source formula at an arbitrary
    PA-model variable name, calibrated to the parameter-expression compiler. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SourceFiniteParameters SourceFiniteParameterSubstitution SubstitutionSource
  NumericalSubstitutionMaps NumericalInstantiation.
Unset Implicit Arguments.

Definition source_singleton_parameter_names i :=
  match i with 0=>CEvar 0 | S j=>CEconst j end.

Theorem source_finite_parameter_instantiation M phi rho out :
  code_relation M rho (source_parameter_expression source_singleton_parameter_names phi) out ->
  numerical_instantiation M (code_numeral M (sf_encode phi)) (rho 0) out.
Proof.
  intro HO. destruct (substitution_singleton_total M (rho 0)) as (b&c&HHead&HTail).
  exists b,c. split;[exact HHead|].
  apply (source_finite_parameter_substitution M phi source_singleton_parameter_names
    rho b c (succM M (zeroM M)) (zeroM M) out);[|exact HO].
  intros [|i] x HX;cbn [source_singleton_parameter_names] in HX.
  - change (x=rho 0) in HX. now subst x.
  - change (x=code_numeral M i) in HX. subst x. exact (HTail (code_numeral M i)).
Qed.

Print Assumptions source_finite_parameter_instantiation.
