(** Calibrate fixed domain/extension roles independently of the query value. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 OldNamedSyntaxBridge OldFullNDSourceBridge SourceFiniteParameters SourceFiniteNameParameters
 SourceParameterGraphs SourceParameterIdentityCalibration SourceNamedFiniteCalibration SourceEnvFDomainWitnessFixed.
From Undecidability.FOL Require Import Syntax.Bounded.
From OldZFC Require Z_base Z_cl Z_rel.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Definition lookup_fixed_index(i:nat):nat:=match i with 0=>1|1=>0|2=>4|3=>3|4=>2|_=>i end.
Definition lookup_fixed_sigma i:sf_term:=C.var(lookup_fixed_index i).
Definition lookup_fixed_roles M value(i:nat):carrier M:=match i with
 |0=>code_numeral M 1|1=>zeroM M|2=>code_numeral M 4|3=>code_numeral M 3|4=>code_numeral M 2|_=>value end.
Lemma source_parameter_lookup_fixed M value phi out:
 bounded 5 phi ->code_relation M(lookup_fixed_roles M value)
  (source_parameter_expression(source_finite_parameter_names 6)phi)out ->
 out=code_numeral M(sf_encode(C.subst_form lookup_fixed_sigma phi)).
Proof.
 intros HB HG.
 assert(HNames:forall i x,(i<5)%nat ->
  (code_relation M(lookup_fixed_roles M value)(source_finite_parameter_names 6 i)x <->
   code_relation M(fun _=>zeroM M)(CEconst(sf_index(lookup_fixed_sigma i)))x)).
 { intros[|[|[|[|[|i]]]]] x HI;try lia;reflexivity. }
 pose proof(proj1(source_parameter_graph_ext M 5 phi HB(source_finite_parameter_names 6)
  (fun i=>CEconst(sf_index(lookup_fixed_sigma i)))(lookup_fixed_roles M value)(fun _=>zeroM M)HNames out)HG)as H.
 exact(code_relation_functional M _ _ out _ H(source_parameter_substitution_calibration M phi lookup_fixed_sigma)).
Qed.
Definition lookup_domain_source:sf_form:=isolated_formula(OldZFC.Z_base.Dom0(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1)).
Definition lookup_extension_source:sf_form:=isolated_formula(OldZFC.Z_cl.Ext0(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 2)(@OC.var OB.sig_empty 3)).
Lemma lookup_domain_source_bound:bounded 5 lookup_domain_source.
Proof.
 apply(@isolated_bounded OC.falsity_on 5(OldZFC.Z_base.Dom0(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1))).
 apply OldZFC.Z_rel.fb_bounded,OldZFC.Z_rel.fbb_fb. reflexivity.
Qed.
Lemma lookup_extension_source_bound:bounded 5 lookup_extension_source.
Proof.
 apply(@isolated_bounded OC.falsity_on 5(OldZFC.Z_cl.Ext0(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 2)(@OC.var OB.sig_empty 3))).
 apply OldZFC.Z_rel.fb_bounded,OldZFC.Z_rel.fbb_fb. reflexivity.
Qed.
Lemma lookup_domain_source_shape:C.subst_form lookup_fixed_sigma lookup_domain_source=ew_domain 1 0.
Proof.
 pose proof(isolated_formula_subst(OldZFC.Z_base.Dom0(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1))
  (fun i=>@OC.var OB.sig_empty(lookup_fixed_index i))lookup_fixed_sigma ltac:(intro i;reflexivity))as E.
 rewrite OldZFC.Z_base.Dom0_subst in E. exact(eq_sym E).
Qed.
Lemma lookup_extension_source_shape:C.subst_form lookup_fixed_sigma lookup_extension_source=ew_extension143.
Proof.
 rewrite ew_extension143_shape.
 pose proof(isolated_formula_subst(OldZFC.Z_cl.Ext0(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 2)(@OC.var OB.sig_empty 3))
  (fun i=>@OC.var OB.sig_empty(lookup_fixed_index i))lookup_fixed_sigma ltac:(intro i;reflexivity))as E.
 rewrite OldZFC.Z_cl.Ext0_subst in E. exact(eq_sym E).
Qed.
Print Assumptions source_parameter_lookup_fixed.
Print Assumptions lookup_domain_source_shape.
Print Assumptions lookup_extension_source_shape.
