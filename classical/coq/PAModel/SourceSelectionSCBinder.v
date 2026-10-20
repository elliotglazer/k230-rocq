(** Literal named existential presentation of the fixed SC selection
    predicate, with arbitrary PA-model names for all free roles. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceBounded
 SourceDefinabilityPrimitives SourceFiniteParameters SourceFiniteNameParameters SourceFiniteParameterNamedBinder
 SourceFiniteParameterComposition SourceParameterGraphs SourceFiniteParameterProofs SourceEnvInClosureConstructor
 SourceNamedQuantifierRules SourceEnvironmentCarrierClosure OldNamedSyntaxBridge OldFullNDSourceBridge.
From OldZFC Require Z_cl Z_rel.
From Undecidability.FOL Require Import Syntax.Facts Syntax.Bounded Sets.minZF.
From Stdlib Require Import Lia Arith.PeanoNat.
Open Scope minZFsyn.
Unset Implicit Arguments.
Definition local_SC_extension_sigma i:sf_term:=match i with 0=>$2|1=>$0|2=>$3|_=>$(i)end.
Definition source_local_SC_body:sf_form:=($0 ∈' $1)∧source_def_extension021[local_SC_extension_sigma].
Definition source_local_SC:sf_form:=∃source_local_SC_body.
Definition source_local_SC_expression:=source_parameter_expression(source_finite_parameter_names 3)source_local_SC.
Definition local_SC_names {A}(representative old value:A)i:=match i with 0=>representative|1=>old|_=>value end.
Lemma source_local_SC_literal:source_local_SC=isolated_formula
 (OldZFC.Z_cl.SC(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 2)).
Proof. reflexivity. Qed.
Lemma source_local_SC_body_bound:bounded 4 source_local_SC_body.
Proof.
 change(bounded 4(isolated_formula(@OC.bin OB.sig_empty OS.ZFSignature.ZF_pred_sig OC.FullSyntax.full_operators OC.falsity_on OC.FullSyntax.Conj
  (@OC.atom OB.sig_empty OS.ZFSignature.ZF_pred_sig OC.FullSyntax.full_operators OC.falsity_on OS.elem
   (Vector.cons _ (@OC.var OB.sig_empty 0) _ (Vector.cons _ (@OC.var OB.sig_empty 1) _ (Vector.nil _))))
  (OldZFC.Z_cl.Ext0(@OC.var OB.sig_empty 2)(@OC.var OB.sig_empty 3)(@OC.var OB.sig_empty 0))))).
 apply(@isolated_bounded OC.falsity_on 4),OldZFC.Z_rel.fb_bounded,OldZFC.Z_rel.fbb_fb. reflexivity.
Qed.
Theorem source_local_SC_named_binder M representative old value witness extension member pair sc:
 witness<>representative ->witness<>old ->witness<>value ->
 code_relation M(EIC_ext_roles old witness value)EIC_ext_expression extension ->
 sf_relation M SFMember witness representative member ->sf_relation M SFAnd member extension pair ->
 code_relation M(local_SC_names representative old value)source_local_SC_expression sc ->
 source_named_quantifier M false witness pair sc.
Proof.
 intros WR WO WV HExt HMember HPair HSC.
 set(rho:=local_SC_names representative old value).
 assert(HBody:code_relation M(finite_binder_environment witness rho)
  (source_parameter_expression(source_finite_parameter_names 4)source_local_SC_body)pair).
 { unfold source_local_SC_body. cbn[source_parameter_expression].
   eapply environment_carrier_code_join;[| |exact HPair].
   - eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HMember].
   - rewrite source_parameter_substitution.
     apply(proj2(source_parameter_graph_ext M 3 source_def_extension021 source_def_extension_bound
      (fun i=>source_finite_parameter_names 4(sf_index(local_SC_extension_sigma i)))source_three_parameter_names
      (finite_binder_environment witness rho)(EIC_ext_roles old witness value)
      ltac:(intros[|[|[|i]]]v HI;try lia;reflexivity)extension)).
     exact HExt. }
 apply(source_finite_parameter_named_binder M 3 source_local_SC_body rho witness pair sc false).
 - exact source_local_SC_body_bound.
 - intros[|[|[|i]]]HI;try lia;cbn[rho local_SC_names];assumption.
 - exact HBody.
 - exact HSC.
Qed.
Print Assumptions source_local_SC_literal.
Print Assumptions source_local_SC_named_binder.
