(** Finite literal bounds and deterministic high-name allocation for the
    local definability constructor. The only external induction is over
    the fixed finite list of auxiliary roles. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes
 SourceBounded SourceBoundMonotone SourceNamedVacuity SourceNamedElimination NumericalContexts
 SourceFiniteParameters SourceFiniteNameParameters SourceParameterGraphs SourceParameterVacuity
 SourceLocalDefinabilityUnpack SourceLocalDefinabilityContent SourceLocalSelectedSubset SourceSelectionSCBinder
 SourceRepresentationClosureRecipe SourceLocalNamedClosureExistence SourceLocalSelectionExistsGraph
 SourceLocalParameterReindex SourceFiniteParameterComposition SourceDefinabilityPrimitives
 OldNamedSyntaxBridge OldFullNDSourceBridge.
From OldZFC Require Z_rel.
From Undecidability.FOL Require Import Syntax.Bounded.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import Lia Arith.PeanoNat.
Unset Implicit Arguments.
Definition source_local_high_name M base n:=Nat.iter n(succM M)base.
Lemma source_local_high_name_order M base i j:(i<j)%nat ->coding_lt M(source_local_high_name M base i)(source_local_high_name M base j).
Proof.
 revert i. induction j as[|j IH];intros i HI;[lia|].
 destruct(Nat.eq_dec i j)as[->|HNeq].
 - change(coding_lt M(source_local_high_name M base j)(succM M(source_local_high_name M base j))). apply coding_lt_succ.
 - change(coding_lt M(source_local_high_name M base i)(succM M(source_local_high_name M base j))).
   exact(coding_lt_trans M _ _ _(IH i ltac:(lia))(coding_lt_succ M _)).
Qed.
Lemma source_local_high_name_above M base i:coding_lt M base(succM M(source_local_high_name M base i)).
Proof.
 destruct i as[|i];[apply coding_lt_succ|].
 exact(coding_lt_trans M _ _ _(source_local_high_name_order M base 0(S i)ltac:(lia))(coding_lt_succ M _)).
Qed.
Lemma source_local_high_name_distinct M base i j:(i<>j)%nat ->source_local_high_name M base i<>source_local_high_name M base j.
Proof.
 intro H. destruct(Nat.lt_trichotomy i j)as[HI|[E|HJ]];[|contradiction|].
 - exact(@Peano.lt_neq(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)_ _(source_local_high_name_order M base i j HI)).
 - intro E. exact(@Peano.lt_neq(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)_ _(source_local_high_name_order M base j i HJ)(Logic.eq_sym E)).
Qed.
Theorem source_named_context_vacuous_above_bound M b c n k x:
 context_bounded M b c n k ->coding_lt M k(succM M x) ->source_named_context_vacuous M b c n x.
Proof. intros HC HX f HF. exact(source_named_vacuous_above_bound M f x k(HC f HF)HX). Qed.
Lemma source_local_def_predicate_bound:bounded 2 source_local_def_predicate.
Proof. unfold source_local_def_predicate. apply(@isolated_bounded OC.falsity_on 2),OldZFC.Z_rel.fb_bounded,OldZFC.Z_rel.fbb_fb. reflexivity. Qed.
Lemma source_local_SC_bound:bounded 3 source_local_SC.
Proof. constructor;exact source_local_SC_body_bound. Qed.
Lemma source_local_subset_bound:bounded 2 source_local_subset.
Proof. constructor;exact source_local_subset_body_bound. Qed.
Theorem source_local_condition_three_roles M carrier successor closure succ cl:
 code_relation M(local_subset_names carrier successor)source_local_successor_expression succ ->
 code_relation M(local_subset_names successor closure)source_local_closure_expression cl ->
 code_relation M(local_closure_roles carrier successor closure)representation_successor_expression succ /\
 code_relation M(local_closure_roles carrier successor closure)representation_closure_expression cl.
Proof.
 intros HS HC. split.
 - apply(proj2(source_parameter_graph_ext M 2 source_def_successor01 source_def_successor_bound
    (source_finite_parameter_names 3)(source_finite_parameter_names 2)(local_closure_roles carrier successor closure)
    (local_subset_names carrier successor)ltac:(intros[|[|i]]x HI;try lia;reflexivity)succ)). exact HS.
 - change(code_relation M(local_closure_roles carrier successor closure)
    (source_parameter_expression(source_finite_parameter_names 3)(source_local_closure01[local_selection_closure_sigma]))cl).
   apply(source_local_parameter_reindex M 2 source_local_closure01(source_finite_parameter_names 3)
    local_selection_closure_sigma(local_closure_roles carrier successor closure)(local_subset_names successor closure)cl source_local_closure_bound);[|exact HC].
   intros[|[|i]]HI;try lia;reflexivity.
Qed.
Print Assumptions source_local_high_name_order.
Print Assumptions source_local_high_name_distinct.
Print Assumptions source_named_context_vacuous_above_bound.
Print Assumptions source_local_def_predicate_bound.
Print Assumptions source_local_condition_three_roles.
