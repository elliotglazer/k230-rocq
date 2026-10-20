(** Ordinary closure antecedents independent of the next-attempt witness. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourceQuantifierRules
 SourceRecursionPrimitiveRelations SourceRecursionAttempt SourceRecursionAttemptBounds SourceRecursionShiftGraphs
 SourceRecursionRangeBackground SourceRecursionRangeChart SourceRecursionExtensionInputShift SourceRecursionAtomicShift.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition source_rec_closure_next_inputs M phi o a N f z v next Y A:=exists background af mz appf mnext chart successor,
 A=background++[af;mz;appf;mnext;chart;successor] /\source_rec_rr_background M phi o N background /\
 source_rec_attempt M phi o a N f af /\sf_relation M SFMember z N mz /\source_rec_app M f z v appf /\
 sf_relation M SFMember next N mnext /\source_rec_range_chart M phi o a N Y chart /\source_rec_successor M z next successor.
Theorem source_rec_closure_next_inputs_total M phi o a N f z v next Y:exists A,source_rec_closure_next_inputs M phi o a N f z v next Y A.
Proof.
 destruct(source_rec_rr_background_total M phi o N)as(background&HBack).
 destruct(source_rec_attempt_total M phi o a N f)as(af&HAF).
 destruct(sf_relation_total M SFMember z N)as(mz&HMZ).
 destruct(source_rec_app_total M f z v)as(appf&HAppF).
 destruct(sf_relation_total M SFMember next N)as(mnext&HMNext).
 destruct(source_rec_range_chart_total M phi o a N Y)as(chart&HChart).
 destruct(source_rec_successor_total M z next)as(successor&HS).
 exists(background++[af;mz;appf;mnext;chart;successor]),background,af,mz,appf,mnext,chart,successor. split;[reflexivity|]. auto 10.
Qed.
Theorem source_rec_closure_next_inputs_bounded M phi o a N f z v next Y A k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M f k ->
 coding_lt M z k ->coding_lt M v k ->coding_lt M next k ->coding_lt M Y k ->source_rec_closure_next_inputs M phi o a N f z v next Y A ->forall x,In x A ->source_bounded M x k.
Proof.
 intros BP BO BA BN BF BZ BV BNext BY(background&af&mz&appf&mnext&chart&successor&E&HBack&HAF&HMZ&HAppF&HMNext&HChart&HS).
 subst A. intros x HX. apply in_app_or in HX. destruct HX as[HX|HX].
 - exact(source_rec_rr_background_bounded M phi o N background k BP BO BN HBack x HX).
 - destruct HX as[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
   + exact(source_rec_attempt_bounded M phi o a N f af k BP BO BA BN BF HAF).
   + exact(proj2(source_bounded_accept_atom M SFMember z N mz k(or_introl eq_refl)HMZ)(conj BZ BN)).
   + exact(source_rec_app_bounded M f z v appf k BF BZ BV HAppF).
   + exact(proj2(source_bounded_accept_atom M SFMember next N mnext k(or_introl eq_refl)HMNext)(conj BNext BN)).
   + exact(source_rec_range_chart_bounded M phi o a N Y chart k BP BO BA BN BY HChart).
   + exact(source_rec_successor_bounded M z next successor k BZ BNext HS).
Qed.
Theorem source_rec_closure_next_inputs_shift M phi o a N f z v next Y A AS:
 source_bounded M phi(code_numeral M 2) ->source_rec_closure_next_inputs M phi o a N f z v next Y A ->
 source_rec_closure_next_inputs M phi(succM M o)(succM M a)(succM M N)(succM M f)(succM M z)(succM M v)(succM M next)(succM M Y)AS ->Forall2(source_formula_shift M)A AS.
Proof.
 intros BP(background&af&mz&appf&mnext&chart&successor&E&HBack&HAF&HMZ&HAppF&HMNext&HChart&HS)
 (backgroundS&afS&mzS&appfS&mnextS&chartS&successorS&ES&HBackS&HAFS&HMZS&HAppFS&HMNextS&HChartS&HSS). subst A AS.
 apply Forall2_app;[exact(source_rec_rr_background_shift M phi o N background backgroundS BP HBack HBackS)|].
 constructor;[exact(source_rec_attempt_shift M phi o a N f af afS BP HAF HAFS)|].
 constructor;[exact(source_rec_member_shift M z N mz mzS HMZ HMZS)|].
 constructor;[exact(source_rec_app_shift M f z v appf appfS HAppF HAppFS)|].
 constructor;[exact(source_rec_member_shift M next N mnext mnextS HMNext HMNextS)|].
 constructor;[exact(source_rec_range_chart_shift M phi o a N Y chart chartS BP HChart HChartS)|].
 constructor;[exact(source_rec_successor_shift M z next successor successorS HS HSS)|constructor].
Qed.
Print Assumptions source_rec_closure_next_inputs_total.
Print Assumptions source_rec_closure_next_inputs_bounded.
Print Assumptions source_rec_closure_next_inputs_shift.
