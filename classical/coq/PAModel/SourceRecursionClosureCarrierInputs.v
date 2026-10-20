(** Ordinary closure background at a named range carrier, independent of index and value witnesses. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SourceBounded SourceQuantifierRules SourceRecursionRangeBackground SourceRecursionRangeChart SourceRecursionExAOn.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition source_rec_closure_carrier_inputs M phi o a N Y A:=exists background chart allExA,
 A=background++[chart;allExA] /\source_rec_rr_background M phi o N background /\source_rec_range_chart M phi o a N Y chart /\source_rec_exa_on M phi o a N allExA.
Theorem source_rec_closure_carrier_inputs_total M phi o a N Y:exists A,source_rec_closure_carrier_inputs M phi o a N Y A.
Proof.
 destruct(source_rec_rr_background_total M phi o N)as(background&HBack).
 destruct(source_rec_range_chart_total M phi o a N Y)as(chart&HChart).
 destruct(source_rec_exa_on_total M phi o a N)as(allExA&HAll).
 exists(background++[chart;allExA]),background,chart,allExA. split;[reflexivity|]. auto.
Qed.
Theorem source_rec_closure_carrier_inputs_bounded M phi o a N Y A k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M Y k ->
 source_rec_closure_carrier_inputs M phi o a N Y A ->forall x,In x A ->source_bounded M x k.
Proof.
 intros BP BO BA BN BY(background&chart&allExA&E&HBack&HChart&HAll). subst A.
 intros x HX. apply in_app_or in HX. destruct HX as[HX|[<-|[<-|[]]]].
 - exact(source_rec_rr_background_bounded M phi o N background k BP BO BN HBack x HX).
 - exact(source_rec_range_chart_bounded M phi o a N Y chart k BP BO BA BN BY HChart).
 - exact(source_rec_exa_on_bounded M phi o a N allExA k BP BO BA BN HAll).
Qed.
Theorem source_rec_closure_carrier_inputs_shift M phi o a N Y A AS:
 source_bounded M phi(code_numeral M 2) ->source_rec_closure_carrier_inputs M phi o a N Y A ->
 source_rec_closure_carrier_inputs M phi(succM M o)(succM M a)(succM M N)(succM M Y)AS ->Forall2(source_formula_shift M)A AS.
Proof.
 intros BP(background&chart&allExA&E&HBack&HChart&HAll)(backgroundS&chartS&allExAS&ES&HBackS&HChartS&HAllS). subst A AS.
 apply Forall2_app;[exact(source_rec_rr_background_shift M phi o N background backgroundS BP HBack HBackS)|].
 constructor;[exact(source_rec_range_chart_shift M phi o a N Y chart chartS BP HChart HChartS)|].
 constructor;[exact(source_rec_exa_on_shift M phi o a N allExA allExAS BP HAll HAllS)|constructor].
Qed.
Print Assumptions source_rec_closure_carrier_inputs_total.
Print Assumptions source_rec_closure_carrier_inputs_bounded.
Print Assumptions source_rec_closure_carrier_inputs_shift.
