(** The actual extension-existence certificate with any hygienic output name. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceFiniteParameterNamedBinder
 SourceFiniteParameters SourceFiniteNameParameters SourceFiniteParameterProofs SourceParameterGraphs SourceFiniteParameterComposition
 SourceDefinabilityPrimitives SourceProjectionOperationFixed SourceEnvironmentExtensionScopes SourceNamedQuantifierRules
 OldNamedSyntaxBridge OldFullNDSourceBridge SourceZFRProvability.
From OldZFC Require Z_cl Z_rel.
From Undecidability.FOL Require Import Syntax.Facts Syntax.Bounded Sets.minZF.
From Stdlib Require Import Lia.
Open Scope minZFsyn.
Unset Implicit Arguments.
Definition projection_extension_body3:sf_form:=isolated_formula(OldZFC.Z_cl.Ext0
 (@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 2)(@OC.var OB.sig_empty 0)).
Lemma projection_extension_body_bound:CBound.bounded 3 projection_extension_body3.
Proof. unfold projection_extension_body3. apply(@isolated_bounded OC.falsity_on 3),OldZFC.Z_rel.fb_bounded,OldZFC.Z_rel.fbb_fb. reflexivity. Qed.
Definition projection_extension_exists_sigma i:sf_term:=match i with 0=>$1|1=>$0|_=>$2 end.
Lemma projection_extension_body_literal:projection_extension_body3=source_def_extension021[projection_extension_exists_sigma].
Proof. reflexivity. Qed.
Definition projection_two_values {A}(p a:A)i:=match i with 0=>p|_=>a end.
Theorem source_projection_extension_named_exists M p a e extension result:
 e<>p ->e<>a ->
 code_relation M(environment_extension_names M p e a)
  (source_parameter_expression source_three_parameter_names source_def_extension021)extension ->
 code_relation M(projection_two_values p a)source_projection_extension_expression result ->
 source_named_quantifier M false e extension result.
Proof.
 intros EP EA HExt HResult.
 apply(source_finite_parameter_named_binder M 2 projection_extension_body3(projection_two_values p a)e extension result false).
 - exact projection_extension_body_bound.
 - intros[|[|i]]HI;try lia;assumption.
 - rewrite projection_extension_body_literal,source_parameter_substitution.
   apply(proj2(source_parameter_graph_ext M 3 source_def_extension021 source_def_extension_bound
    (fun i=>source_finite_parameter_names 3(sf_index(projection_extension_exists_sigma i)))source_three_parameter_names
    (finite_binder_environment e(projection_two_values p a))(environment_extension_names M p e a)
    ltac:(intros[|[|[|i]]]v HI;try lia;reflexivity)extension)). exact HExt.
 - exact HResult.
Qed.
Theorem source_zfr_projection_extension_named_total M p a e extension:
 e<>p ->e<>a ->
 code_relation M(environment_extension_names M p e a)
  (source_parameter_expression source_three_parameter_names source_def_extension021)extension ->
 exists result,source_named_quantifier M false e extension result /\source_zfr_provable M result.
Proof.
 intros EP EA HE. destruct(code_relation_total M source_projection_extension_expression(projection_two_values p a))as(result&HR).
 exists result. split.
 - exact(source_projection_extension_named_exists M p a e extension result EP EA HE HR).
 - exact(source_zfr_projection_extension M(projection_two_values p a)result HR).
Qed.
Print Assumptions source_projection_extension_named_exists.
Print Assumptions source_zfr_projection_extension_named_total.
