(** Actual Def witness in the same fixed closed context, with a named fresh witness. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes NumericalContexts NumericalSourceFull
 SourceFiniteParameters SourceFiniteNameParameters SourceFiniteParameterNamedBinder SourceParameterGraphs
 SourceLocalDefinabilityFixed SourceLocalDefinabilityContext SourceLocalDefinabilityUnpack SourceLocalParameterReindex
 SourceNamedQuantifierRules SourceProofWeakening OldNamedSyntaxBridge OldFullNDSourceBridge.
From OldZFC Require Z_cl Z_rel.
From Undecidability.FOL Require Import Syntax.Bounded Syntax.Facts Sets.minZF.
From Stdlib Require Import Lia.
Open Scope minZFsyn.
Unset Implicit Arguments.
Definition source_local_def_exists_body:sf_form:=isolated_formula
 (OldZFC.Z_cl.Def0(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 0)).
Definition source_local_def_swap i:sf_term:=match i with 0=>$1|_=>$0 end.
Lemma source_local_def_exists_body_swap:
 source_local_def_exists_body=source_local_def_predicate[source_local_def_swap].
Proof. reflexivity. Qed.
Lemma source_local_def_predicate_bound:bounded 2 source_local_def_predicate.
Proof. unfold source_local_def_predicate. apply(@isolated_bounded OC.falsity_on 2),OldZFC.Z_rel.fb_bounded,OldZFC.Z_rel.fbb_fb. reflexivity. Qed.
Lemma source_local_def_exists_body_bound:bounded 2 source_local_def_exists_body.
Proof. unfold source_local_def_exists_body. apply(@isolated_bounded OC.falsity_on 2),OldZFC.Z_rel.fb_bounded,OldZFC.Z_rel.fbb_fb. reflexivity. Qed.
Theorem source_local_def_exists_named_graph M carrier definables predicate out:
 definables<>carrier ->
 code_relation M(local_def_names carrier definables)source_local_def_predicate_expression predicate ->
 code_relation M(fun _:nat=>carrier)source_local_def_exists_expression out ->
 source_named_quantifier M false definables predicate out.
Proof.
 intros DA HDef HOut.
 apply(source_finite_parameter_named_binder M 1 source_local_def_exists_body(fun _:nat=>carrier)definables predicate out false).
 - exact source_local_def_exists_body_bound.
 - intros i HI. exact DA.
 - rewrite source_local_def_exists_body_swap.
   apply(source_local_parameter_reindex M 2 source_local_def_predicate(source_finite_parameter_names 2)
    source_local_def_swap(finite_binder_environment definables(fun _:nat=>carrier))
    (local_def_names carrier definables)predicate).
   + exact source_local_def_predicate_bound.
   + intros[|[|i]]HI;try lia;reflexivity.
   + exact HDef.
 - exact HOut.
Qed.
Theorem source_full_local_def_exists M fb fc fn gb gc gn carrier definables predicate out k:
 source_local_fixed_context M fb fc fn ->context_included M fb fc fn gb gc gn ->context_bounded M gb gc gn k ->
 definables<>carrier ->
 code_relation M(local_def_names carrier definables)source_local_def_predicate_expression predicate ->
 code_relation M(fun _:nat=>carrier)source_local_def_exists_expression out ->
 source_named_quantifier M false definables predicate out /\source_full_prv M gb gc gn out.
Proof.
 intros HF HI HB DA HD HO. split.
 - exact(source_local_def_exists_named_graph M carrier definables predicate out DA HD HO).
 - apply(source_full_prv_weaken_bounded M fb fc fn gb gc gn out k);[|exact HI|exact HB].
   exact(source_full_local_fixed_instance M fb fc fn 0(fun _:nat=>carrier)out HF ltac:(lia)HO).
Qed.
Print Assumptions source_local_def_exists_body_swap.
Print Assumptions source_local_def_exists_named_graph.
Print Assumptions source_full_local_def_exists.
