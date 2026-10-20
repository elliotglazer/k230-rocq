(** Exact Op5 closure-existence graph with an arbitrary named output. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceFiniteParameters SourceFiniteNameParameters
 SourceFiniteParameterNamedBinder SourceParameterGraphs SourceFiniteParameterComposition
 SourceLocalParameterReindex SourceLocalDefinabilityContent SourceLocalSelectedSubset SourceSelectionOperationGraph
 SourceEnvironmentCarrierClosure SourceClosureTernaryFixed SourceClosureCarrierFixed SourceDefinabilityPrimitives
 OldNamedSyntaxBridge OldFullNDSourceBridge SourceNamedQuantifierRules.
From OldZFC Require Z_cl Z_rel.
From Undecidability.FOL Require Import Syntax.Facts Syntax.Bounded Sets.minZF.
From Stdlib Require Import Lia.
Open Scope minZFsyn.
Unset Implicit Arguments.
Definition local_selection_exists_roles {A}(carrier successor closure representative old:A)i:=match i with
 |0=>carrier|1=>successor|2=>closure|3=>representative|4=>old|_=>carrier end.
Definition local_selection_closure_sigma i:sf_term:=match i with 0=>$1|_=>$2 end.
Definition local_selection_output_sigma i:sf_term:=match i with 0=>$4|1=>$5|2=>$6|_=>$0 end.
Definition source_local_selection_exists_body:sf_form:=isolated_formula
 (@OC.bin OB.sig_empty OS.ZFSignature.ZF_pred_sig OC.FullSyntax.full_operators OC.falsity_on OC.FullSyntax.Conj
  (@OC.atom OB.sig_empty OS.ZFSignature.ZF_pred_sig OC.FullSyntax.full_operators OC.falsity_on OS.elem
   (Vector.cons _ (@OC.var OB.sig_empty 0) _ (Vector.cons _ (@OC.var OB.sig_empty 3) _ (Vector.nil _))))
  (OldZFC.Z_cl.Op 5(@OC.var OB.sig_empty 4)(@OC.var OB.sig_empty 5)(@OC.var OB.sig_empty 6)(@OC.var OB.sig_empty 0))).
Definition source_local_selection_exists:sf_form:=∃source_local_selection_exists_body.
Definition source_local_selection_exists_expression:=source_parameter_expression(source_finite_parameter_names 6)source_local_selection_exists.
Lemma source_local_selection_exists_body_bound:bounded 7 source_local_selection_exists_body.
Proof. unfold source_local_selection_exists_body. apply(@isolated_bounded OC.falsity_on 7),OldZFC.Z_rel.fb_bounded,OldZFC.Z_rel.fbb_fb. reflexivity. Qed.
Lemma source_local_selection_exists_body_shell:source_local_selection_exists_body=
 ($0 ∈' $3)∧source_local_operation5[local_selection_output_sigma].
Proof. reflexivity. Qed.
Theorem source_local_selection_exists_named M carrier successor closure representative old selected member operation body ex:
 (forall i,(i<6)%nat ->selected<>local_selection_exists_roles carrier successor closure representative old i) ->
 sf_relation M SFMember selected closure member ->
 code_relation M(local_operation5_names representative old carrier selected)source_local_operation5_expression operation ->
 sf_relation M SFAnd member operation body ->
 code_relation M(local_selection_exists_roles carrier successor closure representative old)source_local_selection_exists_expression ex ->
 source_named_quantifier M false selected body ex.
Proof.
 intros HF HM HO HB HE.
 apply(source_finite_parameter_named_binder M 6 source_local_selection_exists_body
  (local_selection_exists_roles carrier successor closure representative old)selected body ex false).
 - exact source_local_selection_exists_body_bound.
 - exact HF.
 - rewrite source_local_selection_exists_body_shell. cbn[source_parameter_expression].
   eapply environment_carrier_code_join;[| |exact HB].
   + eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HM].
   + apply(source_local_parameter_reindex M 4 source_local_operation5(source_finite_parameter_names 7)
      local_selection_output_sigma(finite_binder_environment selected(local_selection_exists_roles carrier successor closure representative old))
      (local_operation5_names representative old carrier selected)operation source_local_operation5_bound);[|exact HO].
     intros[|[|[|[|i]]]]HI;try lia;reflexivity.
 - exact HE.
Qed.
Lemma source_local_selection_closure_law_shell:source_closure_ternary_law 5=
 source_def_successor01→source_local_closure01[local_selection_closure_sigma]→
 ($3 ∈' $2)→($4 ∈' $2)→($5 ∈' $2)→source_local_selection_exists.
Proof. reflexivity. Qed.
Theorem source_local_selection_closure_law_graph M carrier successor closure representative old succ cl repmem oldmem carriermem ex l1 l2 l3 l4 law:
 code_relation M(local_subset_names carrier successor)source_local_successor_expression succ ->
 code_relation M(local_subset_names successor closure)source_local_closure_expression cl ->
 sf_relation M SFMember representative closure repmem ->sf_relation M SFMember old closure oldmem ->
 sf_relation M SFMember carrier closure carriermem ->
 code_relation M(local_selection_exists_roles carrier successor closure representative old)source_local_selection_exists_expression ex ->
 sf_relation M SFImpl carriermem ex l1 ->sf_relation M SFImpl oldmem l1 l2 ->
 sf_relation M SFImpl repmem l2 l3 ->sf_relation M SFImpl cl l3 l4 ->sf_relation M SFImpl succ l4 law ->
 code_relation M(local_selection_exists_roles carrier successor closure representative old)(source_closure_ternary_expression 5)law.
Proof.
 intros HS HC HR HE HA HX H1 H2 H3 H4 HL.
 set(rho:=local_selection_exists_roles carrier successor closure representative old).
 assert(GS:code_relation M rho(source_parameter_expression(source_finite_parameter_names 6)source_def_successor01)succ).
 { apply(proj2(source_parameter_graph_ext M 2 source_def_successor01 source_def_successor_bound
    (source_finite_parameter_names 6)(source_finite_parameter_names 2)rho(local_subset_names carrier successor)
    ltac:(intros[|[|i]]x HI;try lia;reflexivity)succ)). exact HS. }
 assert(GC:code_relation M rho(source_parameter_expression(source_finite_parameter_names 6)
  (source_local_closure01[local_selection_closure_sigma]))cl).
 { apply(source_local_parameter_reindex M 2 source_local_closure01(source_finite_parameter_names 6)
    local_selection_closure_sigma rho(local_subset_names successor closure)cl source_local_closure_bound);[|exact HC].
   intros[|[|i]]HI;try lia;reflexivity. }
 unfold source_closure_ternary_expression. rewrite source_local_selection_closure_law_shell. cbn[source_parameter_expression].
 eapply environment_carrier_code_join;[exact GS| |exact HL].
 eapply environment_carrier_code_join;[exact GC| |exact H4].
 eapply environment_carrier_code_join;[| |exact H3];[eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HR]|].
 eapply environment_carrier_code_join;[| |exact H2];[eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HE]|].
 eapply environment_carrier_code_join;[|exact HX|exact H1]. eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HA].
Qed.
Lemma source_local_carrier_law_shell:source_closure_carrier_law=
 source_def_successor01→source_local_closure01[local_selection_closure_sigma]→($0 ∈' $2).
Proof. reflexivity. Qed.
Theorem source_local_carrier_law_graph M carrier successor closure succ cl member middle law:
 code_relation M(local_subset_names carrier successor)source_local_successor_expression succ ->
 code_relation M(local_subset_names successor closure)source_local_closure_expression cl ->
 sf_relation M SFMember carrier closure member ->sf_relation M SFImpl cl member middle ->sf_relation M SFImpl succ middle law ->
 code_relation M(fun i=>match i with 0=>carrier|1=>successor|_=>closure end)source_closure_carrier_expression law.
Proof.
 intros HS HC HM HI HO. set(rho:=fun i=>match i with 0=>carrier|1=>successor|_=>closure end).
 assert(GS:code_relation M rho(source_parameter_expression(source_finite_parameter_names 3)source_def_successor01)succ).
 { apply(proj2(source_parameter_graph_ext M 2 source_def_successor01 source_def_successor_bound
    (source_finite_parameter_names 3)(source_finite_parameter_names 2)rho(local_subset_names carrier successor)
    ltac:(intros[|[|i]]x HX;try lia;reflexivity)succ)). exact HS. }
 assert(GC:code_relation M rho(source_parameter_expression(source_finite_parameter_names 3)
  (source_local_closure01[local_selection_closure_sigma]))cl).
 { apply(source_local_parameter_reindex M 2 source_local_closure01(source_finite_parameter_names 3)
    local_selection_closure_sigma rho(local_subset_names successor closure)cl source_local_closure_bound);[|exact HC].
   intros[|[|i]]HX;try lia;reflexivity. }
 unfold source_closure_carrier_expression. rewrite source_local_carrier_law_shell. cbn[source_parameter_expression].
 eapply environment_carrier_code_join;[exact GS| |exact HO].
 eapply environment_carrier_code_join;[exact GC| |exact HI]. eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HM].
Qed.
Print Assumptions source_local_selection_exists_named.
Print Assumptions source_local_selection_closure_law_graph.
Print Assumptions source_local_carrier_law_graph.
