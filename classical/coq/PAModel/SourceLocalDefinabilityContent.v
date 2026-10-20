(** The literal Def0 witness contents supply successor, closure and
    the chosen-set membership rule in the same arbitrary source context. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceBounded NumericalSourceFull
 SourceDefinabilityPrimitives SourceFiniteParameters SourceFiniteNameParameters
 SourceLocalDefinabilityUnpack SourceLocalDefinabilityAccess SourceLocalParameterReindex SourceLocalSelectedSubset
 SourceFiniteParameterComposition SourceEnvironmentCarrierClosure SourceConjunctionRules
 OldNamedSyntaxBridge OldFullNDSourceBridge.
From OldZFC Require Z_cl Z_rel.
From Undecidability.FOL Require Import Syntax.Facts Syntax.Bounded Sets.minZF.
From Stdlib Require Import Lia.
Open Scope minZFsyn.
Unset Implicit Arguments.
Definition source_local_closure01:sf_form:=isolated_formula
 (OldZFC.Z_cl.Cl(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1)).
Definition source_local_successor_expression:=source_parameter_expression(source_finite_parameter_names 2)source_def_successor01.
Definition source_local_closure_expression:=source_parameter_expression(source_finite_parameter_names 2)source_local_closure01.
Definition local_unpack_successor_sigma i:sf_term:=match i with 0=>$2|_=>$1 end.
Definition local_unpack_closure_sigma i:sf_term:=match i with 0=>$1|_=>$0 end.
Definition local_unpack_access_sigma i:sf_term:=match i with 0=>$0|1=>$2|_=>$3 end.
Lemma source_local_closure_bound:bounded 2 source_local_closure01.
Proof. unfold source_local_closure01. apply(@isolated_bounded OC.falsity_on 2),OldZFC.Z_rel.fb_bounded,OldZFC.Z_rel.fbb_fb. reflexivity. Qed.
Lemma source_local_unpack_content_shell:source_local_unpack_content=
 (source_def_successor01[local_unpack_successor_sigma]∧source_local_closure01[local_unpack_closure_sigma])∧
 source_local_access[local_unpack_access_sigma].
Proof. reflexivity. Qed.
Theorem source_local_unpack_content_graph M carrier definables successor closure succ cl access pair content:
 code_relation M(local_subset_names carrier successor)source_local_successor_expression succ ->
 code_relation M(local_subset_names successor closure)source_local_closure_expression cl ->
 code_relation M(local_access_names closure carrier definables)source_local_access_expression access ->
 sf_relation M SFAnd succ cl pair ->sf_relation M SFAnd pair access content ->
 code_relation M(local_unpack_content_names closure successor carrier definables)
  (source_parameter_expression(source_finite_parameter_names 4)source_local_unpack_content)content.
Proof.
 intros HS HC HA HP HO. rewrite source_local_unpack_content_shell. cbn[source_parameter_expression].
 eapply environment_carrier_code_join;[| |exact HO].
 - eapply environment_carrier_code_join;[| |exact HP].
   + apply(source_local_parameter_reindex M 2 source_def_successor01(source_finite_parameter_names 4)
      local_unpack_successor_sigma(local_unpack_content_names closure successor carrier definables)
      (local_subset_names carrier successor)succ source_def_successor_bound);[|exact HS].
     intros[|[|i]]HI;try lia;reflexivity.
   + apply(source_local_parameter_reindex M 2 source_local_closure01(source_finite_parameter_names 4)
      local_unpack_closure_sigma(local_unpack_content_names closure successor carrier definables)
      (local_subset_names successor closure)cl source_local_closure_bound);[|exact HC].
     intros[|[|i]]HI;try lia;reflexivity.
 - apply(source_local_parameter_reindex M 3 source_local_access(source_finite_parameter_names 4)
    local_unpack_access_sigma(local_unpack_content_names closure successor carrier definables)
    (local_access_names closure carrier definables)access source_local_access_bound);[|exact HA].
   intros[|[|[|i]]]HI;try lia;reflexivity.
Qed.
Theorem source_full_local_unpack_contents M gb gc gn succ cl access pair content:
 sf_relation M SFAnd succ cl pair ->sf_relation M SFAnd pair access content ->
 source_full_prv M gb gc gn content ->
 source_full_prv M gb gc gn succ /\source_full_prv M gb gc gn cl /\source_full_prv M gb gc gn access.
Proof.
 intros HP HO PC. pose proof(source_full_conjunction_left M gb gc gn pair access content HO PC)as PBoth.
 split;[exact(source_full_conjunction_left M gb gc gn succ cl pair HP PBoth)|]. split.
 - exact(source_full_conjunction_right M gb gc gn succ cl pair HP PBoth).
 - exact(source_full_conjunction_right M gb gc gn pair access content HO PC).
Qed.
Print Assumptions source_local_unpack_content_shell.
Print Assumptions source_local_unpack_content_graph.
Print Assumptions source_full_local_unpack_contents.
