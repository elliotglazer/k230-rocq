(** Finite ordinary antecedents independent of the predecessor-value witness. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourceQuantifierRules
 SourceRecursionPrimitiveRelations SourceRecursionAttempt SourceRecursionAttemptBounds SourceRecursionShiftGraphs
 SourceRecursionRangeBackground SourceRecursionRangeChart SourceRecursionExtensionInputShift SourceRecursionAtomicShift.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition source_rec_closure_inputs M phi o a N f g z v w next Y A:=exists background af ag mz appf appnext mnext chart,
 A=background++[af;ag;mz;appf;appnext;mnext;chart] /\source_rec_rr_background M phi o N background /\
 source_rec_attempt M phi o a N f af /\source_rec_attempt M phi o a N g ag /\sf_relation M SFMember z N mz /\
 source_rec_app M f z v appf /\source_rec_app M g next w appnext /\sf_relation M SFMember next N mnext /\source_rec_range_chart M phi o a N Y chart.
Theorem source_rec_closure_inputs_total M phi o a N f g z v w next Y:exists A,source_rec_closure_inputs M phi o a N f g z v w next Y A.
Proof.
 destruct(source_rec_rr_background_total M phi o N)as(background&HBack).
 destruct(source_rec_attempt_total M phi o a N f)as(af&HAF).
 destruct(source_rec_attempt_total M phi o a N g)as(ag&HAG).
 destruct(sf_relation_total M SFMember z N)as(mz&HMZ).
 destruct(source_rec_app_total M f z v)as(appf&HAppF).
 destruct(source_rec_app_total M g next w)as(appnext&HAppNext).
 destruct(sf_relation_total M SFMember next N)as(mnext&HMNext).
 destruct(source_rec_range_chart_total M phi o a N Y)as(chart&HChart).
 exists(background++[af;ag;mz;appf;appnext;mnext;chart]),background,af,ag,mz,appf,appnext,mnext,chart. split;[reflexivity|]. auto 10.
Qed.
Theorem source_rec_closure_inputs_bounded M phi o a N f g z v w next Y A k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M f k ->coding_lt M g k ->
 coding_lt M z k ->coding_lt M v k ->coding_lt M w k ->coding_lt M next k ->coding_lt M Y k ->source_rec_closure_inputs M phi o a N f g z v w next Y A ->
 forall x,In x A ->source_bounded M x k.
Proof.
 intros BP BO BA BN BF BG BZ BV BW BNext BY(background&af&ag&mz&appf&appnext&mnext&chart&E&HBack&HAF&HAG&HMZ&HAppF&HAppNext&HMNext&HChart).
 subst A. intros x HX. apply in_app_or in HX. destruct HX as[HX|HX].
 - exact(source_rec_rr_background_bounded M phi o N background k BP BO BN HBack x HX).
 - destruct HX as[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]].
   + exact(source_rec_attempt_bounded M phi o a N f af k BP BO BA BN BF HAF).
   + exact(source_rec_attempt_bounded M phi o a N g ag k BP BO BA BN BG HAG).
   + exact(proj2(source_bounded_accept_atom M SFMember z N mz k(or_introl eq_refl)HMZ)(conj BZ BN)).
   + exact(source_rec_app_bounded M f z v appf k BF BZ BV HAppF).
   + exact(source_rec_app_bounded M g next w appnext k BG BNext BW HAppNext).
   + exact(proj2(source_bounded_accept_atom M SFMember next N mnext k(or_introl eq_refl)HMNext)(conj BNext BN)).
   + exact(source_rec_range_chart_bounded M phi o a N Y chart k BP BO BA BN BY HChart).
Qed.
Theorem source_rec_closure_inputs_shift M phi o a N f g z v w next Y A AS:
 source_bounded M phi(code_numeral M 2) ->source_rec_closure_inputs M phi o a N f g z v w next Y A ->
 source_rec_closure_inputs M phi(succM M o)(succM M a)(succM M N)(succM M f)(succM M g)(succM M z)(succM M v)(succM M w)(succM M next)(succM M Y)AS ->
 Forall2(source_formula_shift M)A AS.
Proof.
 intros BP(background&af&ag&mz&appf&appnext&mnext&chart&E&HBack&HAF&HAG&HMZ&HAppF&HAppNext&HMNext&HChart)
 (backgroundS&afS&agS&mzS&appfS&appnextS&mnextS&chartS&ES&HBackS&HAFS&HAGS&HMZS&HAppFS&HAppNextS&HMNextS&HChartS). subst A AS.
 apply Forall2_app;[exact(source_rec_rr_background_shift M phi o N background backgroundS BP HBack HBackS)|].
 constructor;[exact(source_rec_attempt_shift M phi o a N f af afS BP HAF HAFS)|].
 constructor;[exact(source_rec_attempt_shift M phi o a N g ag agS BP HAG HAGS)|].
 constructor;[exact(source_rec_member_shift M z N mz mzS HMZ HMZS)|].
 constructor;[exact(source_rec_app_shift M f z v appf appfS HAppF HAppFS)|].
 constructor;[exact(source_rec_app_shift M g next w appnext appnextS HAppNext HAppNextS)|].
 constructor;[exact(source_rec_member_shift M next N mnext mnextS HMNext HMNextS)|].
 constructor;[exact(source_rec_range_chart_shift M phi o a N Y chart chartS BP HChart HChartS)|constructor].
Qed.
Print Assumptions source_rec_closure_inputs_total.
Print Assumptions source_rec_closure_inputs_bounded.
Print Assumptions source_rec_closure_inputs_shift.
