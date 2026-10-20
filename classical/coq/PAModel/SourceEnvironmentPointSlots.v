(** Exact finite Op3/Ext slot calibration for the arbitrary-hole An step.
    This connects the checked fixed mathematical law to the propositional
    program; it introduces no source-proof or standardness premise. *)
From PAModel Require Import Model FiniteCoding CodeExpressions CodeExpressionPlug SetFormulaCodes SourceBounded SourcePropositionalTemplates
 SourceEnvironmentCarrierOld SourceEnvironmentCarrierFixed SourceEnvironmentExtensionProgram
 SourceDefinabilityPrimitives SourceEnvironmentExtensionScopes SourceFiniteParameters
 SourceFiniteNameParameters SourceFiniteParameterProofs SourceFiniteParameterComposition SourceFiniteParameterBounds SourceParameterGraphs
 OldNamedSyntaxBridge OldFullNDSourceBridge.
From OldZFC Require Z_cl Z_rel.
From Undecidability.FOL Require Import Syntax.Facts Syntax.Bounded Sets.minZF.
From Stdlib Require Import Lia.
Open Scope minZFsyn.
Unset Implicit Arguments.
Definition environment_operation_source:sf_form:=isolated_formula
 (OldZFC.Z_cl.Op 3 (@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1)
  (@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 2)).
Definition environment_extension_source345:sf_form:=isolated_formula
 (OldZFC.Z_cl.Ext0 (@OC.var OB.sig_empty 3)(@OC.var OB.sig_empty 4)(@OC.var OB.sig_empty 5)).
Definition environment_extension_fixed_slot i:=match i with
 |0=>source_parameter_expression(source_finite_parameter_names 6)environment_operation_source
 |1=>E_sf SFMember(CEvar 3)(CEvar 0)
 |2=>E_sf SFMember(CEvar 4)(CEvar 1)
 |3=>source_parameter_expression(source_finite_parameter_names 6)environment_extension_source345
 |4=>E_sf SFMember(CEvar 5)(CEvar 2)
 |_=>CEconst 0 end.
Lemma environment_extension_fixed_slots_shape:
 source_environment_extension_point_expression=
 code_plug environment_extension_fixed_slot(source_prop_expression environment_extension_point_law).
Proof. reflexivity. Qed.
Theorem source_environment_extension_fixed_slots M rho values law:
 (forall i,code_relation M rho(environment_extension_fixed_slot i)(values i)) ->
 (code_relation M rho source_environment_extension_point_expression law <->
  code_relation M values(source_prop_expression environment_extension_point_law)law).
Proof.
 intro HV. rewrite environment_extension_fixed_slots_shape. exact(code_relation_plug M rho values
  environment_extension_fixed_slot(source_prop_expression environment_extension_point_law)law HV).
Qed.
Theorem source_environment_extension_fixed_slots_prefix M rho values law:
 (forall i,(i<5)%nat ->code_relation M rho(environment_extension_fixed_slot i)(values i)) ->
 (code_relation M rho source_environment_extension_point_expression law <->
  code_relation M values(source_prop_expression environment_extension_point_law)law).
Proof.
 intro HV. set(v:=fun i=>match i with 0=>values 0|1=>values 1|2=>values 2|3=>values 3|4=>values 4|_=>zeroM M end).
 change(code_relation M rho source_environment_extension_point_expression law <->
  code_relation M v(source_prop_expression environment_extension_point_law)law).
 apply source_environment_extension_fixed_slots.
 intros[|[|[|[|[|i]]]]];cbn[v];try apply HV;try lia;reflexivity.
Qed.
Definition environment_extension_345_sigma i:sf_term:=match i with
 |0=>$3|1=>$5|2=>$4|_=>$(i)end.
Lemma environment_extension_345_shape:
 environment_extension_source345=source_def_extension021[environment_extension_345_sigma].
Proof. reflexivity. Qed.
Theorem source_environment_extension_345_graph M rho extension:
 code_relation M rho(environment_extension_fixed_slot 3)extension <->
 code_relation M(environment_extension_names M(rho 3)(rho 5)(rho 4))
  (source_parameter_expression source_three_parameter_names source_def_extension021)extension.
Proof.
 unfold environment_extension_fixed_slot. rewrite environment_extension_345_shape,source_parameter_substitution.
 apply(source_parameter_graph_ext M 3 source_def_extension021 source_def_extension_bound
  (fun i=>source_finite_parameter_names 6(sf_index(environment_extension_345_sigma i)))
  source_three_parameter_names rho(environment_extension_names M(rho 3)(rho 5)(rho 4))).
 intros[|[|[|i]]] x HI;try lia;reflexivity.
Qed.
Lemma environment_operation_source_bound:bounded 3 environment_operation_source.
Proof.
 apply(@isolated_bounded OC.falsity_on 3),OldZFC.Z_rel.fb_bounded,OldZFC.Z_rel.fbb_fb. reflexivity.
Qed.
Theorem source_environment_operation_bound M rho op k:
 coding_lt M(rho 0)k ->coding_lt M(rho 1)k ->coding_lt M(rho 2)k ->
 code_relation M rho(environment_extension_fixed_slot 0)op ->source_bounded M op k.
Proof.
 intros H0 H1 H2 HO. apply(source_parameter_graph_bounded M 3 environment_operation_source
  environment_operation_source_bound(source_finite_parameter_names 6)rho k);[|exact HO].
 intros[|[|[|i]]] x HI HX;try lia.
 - change(x=rho 0)in HX. now subst x.
 - change(x=rho 1)in HX. now subst x.
 - change(x=rho 2)in HX. now subst x.
Qed.
Print Assumptions source_environment_extension_fixed_slots.
Print Assumptions source_environment_extension_345_graph.
Print Assumptions source_environment_operation_bound.



