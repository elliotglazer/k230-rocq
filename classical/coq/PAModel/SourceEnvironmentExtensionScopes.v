(** Exact finite Ext0 primitive under the An successor's three binders.
 The environment/head/output names are arbitrary PA-model elements. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
 SourceDefinabilityPrimitives SourceFiniteParameters SourceFiniteParameterProofs SourceThreeParameterCommutation
 SourceParameterIdentityCalibration NumericalRenamingMaps SourceNamedScopes SourceNamedScopeBinding.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
Unset Implicit Arguments.
Definition environment_extension_names(M:Model)(p e a:carrier M)i:=match i with 0=>p|1=>e|_=>a end.
Theorem source_environment_extension_scoped M p e a extension:
 e<>p ->a<>p ->a<>e ->
 code_relation M(environment_extension_names M p e a)
  (source_parameter_expression source_three_parameter_names source_def_extension021)extension ->
 named_scope_renaming M[p;e;a]extension(code_numeral M(sf_encode source_def_extension021)).
Proof.
 intros HEP HAP HAE HE.
 destruct(named_scope_map_total M[p;e;a])as(b&c&HMap). exists b,c. split;[exact HMap|].
 apply(source_three_parameter_renaming_commutation M source_def_extension021
  (environment_extension_names M p e a)(fun i=>code_numeral M i)extension
  (code_numeral M(sf_encode source_def_extension021))b c(named_scope_bound M[p;e;a])(code_numeral M 3)).
 - exact source_def_extension_bound.
 - exact HE.
 - apply source_parameter_identity_calibration. intros[|[|[|i]]];reflexivity.
 - intros[|[|[|i]]]HI;try lia;apply HMap;cbn[environment_extension_names].
   + left. auto.
   + right. split;[exact HEP|]. exists(zeroM M). split;[left;auto|reflexivity].
   + right. split;[exact HAP|]. exists(code_numeral M 1). split;[|reflexivity].
     right. split;[exact HAE|]. exists(zeroM M). split;[left;auto|reflexivity].
Qed.
Print Assumptions source_environment_extension_scoped.
