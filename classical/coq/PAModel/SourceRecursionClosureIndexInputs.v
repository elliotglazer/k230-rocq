(** Ordinary closure antecedents independent of the domain-successor witness. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourceQuantifierRules
 SourceRecursionPrimitiveRelations SourceRecursionAttempt SourceRecursionAttemptBounds SourceRecursionShiftGraphs
 SourceRecursionRangeBackground SourceRecursionRangeChart SourceRecursionExAOn SourceRecursionExtensionInputShift SourceRecursionAtomicShift.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition source_rec_closure_index_inputs M phi o a N f z v Y A:=exists background af mz appf chart allExA,
 A=background++[af;mz;appf;chart;allExA] /\source_rec_rr_background M phi o N background /\source_rec_attempt M phi o a N f af /\
 sf_relation M SFMember z N mz /\source_rec_app M f z v appf /\source_rec_range_chart M phi o a N Y chart /\source_rec_exa_on M phi o a N allExA.
Theorem source_rec_closure_index_inputs_total M phi o a N f z v Y:exists A,source_rec_closure_index_inputs M phi o a N f z v Y A.
Proof.
 destruct(source_rec_rr_background_total M phi o N)as(background&HBack).
 destruct(source_rec_attempt_total M phi o a N f)as(af&HAF).
 destruct(sf_relation_total M SFMember z N)as(mz&HMZ).
 destruct(source_rec_app_total M f z v)as(appf&HAppF).
 destruct(source_rec_range_chart_total M phi o a N Y)as(chart&HChart).
 destruct(source_rec_exa_on_total M phi o a N)as(allExA&HAll).
 exists(background++[af;mz;appf;chart;allExA]),background,af,mz,appf,chart,allExA. split;[reflexivity|]. auto 10.
Qed.
Theorem source_rec_closure_index_inputs_bounded M phi o a N f z v Y A k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M f k ->coding_lt M z k ->coding_lt M v k ->coding_lt M Y k ->
 source_rec_closure_index_inputs M phi o a N f z v Y A ->forall x,In x A ->source_bounded M x k.
Proof.
 intros BP BO BA BN BF BZ BV BY(background&af&mz&appf&chart&allExA&E&HBack&HAF&HMZ&HAppF&HChart&HAll). subst A.
 intros x HX. apply in_app_or in HX. destruct HX as[HX|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
 - exact(source_rec_rr_background_bounded M phi o N background k BP BO BN HBack x HX).
 - exact(source_rec_attempt_bounded M phi o a N f af k BP BO BA BN BF HAF).
 - exact(proj2(source_bounded_accept_atom M SFMember z N mz k(or_introl eq_refl)HMZ)(conj BZ BN)).
 - exact(source_rec_app_bounded M f z v appf k BF BZ BV HAppF).
 - exact(source_rec_range_chart_bounded M phi o a N Y chart k BP BO BA BN BY HChart).
 - exact(source_rec_exa_on_bounded M phi o a N allExA k BP BO BA BN HAll).
Qed.
Theorem source_rec_closure_index_inputs_shift M phi o a N f z v Y A AS:
 source_bounded M phi(code_numeral M 2) ->source_rec_closure_index_inputs M phi o a N f z v Y A ->
 source_rec_closure_index_inputs M phi(succM M o)(succM M a)(succM M N)(succM M f)(succM M z)(succM M v)(succM M Y)AS ->Forall2(source_formula_shift M)A AS.
Proof.
 intros BP(background&af&mz&appf&chart&allExA&E&HBack&HAF&HMZ&HAppF&HChart&HAll)
 (backgroundS&afS&mzS&appfS&chartS&allExAS&ES&HBackS&HAFS&HMZS&HAppFS&HChartS&HAllS). subst A AS.
 apply Forall2_app;[exact(source_rec_rr_background_shift M phi o N background backgroundS BP HBack HBackS)|].
 constructor;[exact(source_rec_attempt_shift M phi o a N f af afS BP HAF HAFS)|].
 constructor;[exact(source_rec_member_shift M z N mz mzS HMZ HMZS)|].
 constructor;[exact(source_rec_app_shift M f z v appf appfS HAppF HAppFS)|].
 constructor;[exact(source_rec_range_chart_shift M phi o a N Y chart chartS BP HChart HChartS)|].
 constructor;[exact(source_rec_exa_on_shift M phi o a N allExA allExAS BP HAll HAllS)|constructor].
Qed.
Print Assumptions source_rec_closure_index_inputs_total.
Print Assumptions source_rec_closure_index_inputs_bounded.
Print Assumptions source_rec_closure_index_inputs_shift.
