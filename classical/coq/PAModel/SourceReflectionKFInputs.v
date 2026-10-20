(** Ordinary hypotheses retained while proving the K-closure profile. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 SourceRecursionClosureSyntax SourceRecursionClosureTransport SourceRecursionAtomicShift
 SourceReflectionOrdinalChart SourceReflectionOrdinalChartTransport.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition source_reflection_KF_inputs M phi a Y K x A:=exists chart closure member,
 A=[chart;closure;member] /\source_reflection_ordinal_chart M Y K chart /\source_rec_closure M phi a Y closure /\sf_relation M SFMember x K member.
Theorem source_reflection_KF_inputs_total M phi a Y K x:exists A,source_reflection_KF_inputs M phi a Y K x A.
Proof.
 destruct(source_reflection_ordinal_chart_total M Y K)as(chart&HC).
 destruct(source_rec_closure_total M phi a Y)as(closure&HF).
 destruct(sf_relation_total M SFMember x K)as(member&HM).
 exists[chart;closure;member],chart,closure,member. auto.
Qed.
Theorem source_reflection_KF_inputs_bounded M phi a Y K x A k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M a k ->coding_lt M Y k ->coding_lt M K k ->coding_lt M x k ->
 source_reflection_KF_inputs M phi a Y K x A ->forall f,In f A ->source_bounded M f k.
Proof.
 intros BP BA BY BK BX(chart&closure&member&E&HC&HF&HM). subst A. intros f[<-|[<-|[<-|[]]]].
 - exact(source_reflection_ordinal_chart_bounded M Y K chart k BY BK HC).
 - exact(source_rec_closure_bounded M phi a Y closure k BP BA BY HF).
 - exact(proj2(source_bounded_accept_atom M SFMember x K member k(or_introl eq_refl)HM)(conj BX BK)).
Qed.
Theorem source_reflection_KF_inputs_shift M phi a Y K x A B:
 source_bounded M phi(code_numeral M 2) ->source_reflection_KF_inputs M phi a Y K x A ->
 source_reflection_KF_inputs M phi(succM M a)(succM M Y)(succM M K)(succM M x)B ->Forall2(SourceQuantifierRules.source_formula_shift M)A B.
Proof.
 intros BP(chart&closure&member&E&HC&HF&HM)(chart'&closure'&member'&E'&HC'&HF'&HM'). subst A B.
 constructor;[exact(source_reflection_ordinal_chart_shift M Y K chart chart' HC HC')|].
 constructor;[exact(source_rec_closure_shift M phi a Y closure closure' BP HF HF')|].
 constructor;[exact(source_rec_member_shift M x K member member' HM HM')|constructor].
Qed.
Print Assumptions source_reflection_KF_inputs_total.
Print Assumptions source_reflection_KF_inputs_bounded.
Print Assumptions source_reflection_KF_inputs_shift.
