(** Discharge all-index ExA using its genuine proof, retaining only the seven ordinary recursion assumptions. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded NumericalContexts NumericalSourceFull
 SourceFiniteTelescope SourceZFRFiniteRule SourceRecursionStructureInputs SourceRecursionRangeBackground SourceRecursionExAOn SourceRecursionAttemptsExist
 SourceRecursionRangeChart SourceRecursionClosureCarrierInputs SourceRecursionClosureCarrier SourceRecursionClosureSyntax SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_rec_closure_from_structure M phi o a N Y A chart target law k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M Y k ->
 source_rec_structure_inputs M phi o N A ->source_rec_range_chart M phi o a N Y chart ->source_rec_closure M phi a Y target ->
 source_finite_telescope M(A++[chart])target law ->source_zfr_provable M law.
Proof.
 intros BP BO BA BN BY HA HChart HTarget HLaw.
 pose proof(source_rec_structure_inputs_bounded M phi o N A k BP BO BN HA)as Bounds.
 pose proof(source_rec_range_chart_bounded M phi o a N Y chart k BP BO BA BN BY HChart)as BChart.
 pose proof(source_rec_closure_bounded M phi a Y target k BP BA BY HTarget)as BTarget.
 destruct HA as(funlaw&totalG&nonzero&injective&totality&induction&member&E&HFun&HG&HNZ&HInj&HT&HI&HM). subst A.
 destruct(source_rec_exa_on_total M phi o a N)as(allExA&HAll).
 destruct(source_finite_telescope_total M[totalG;nonzero;injective;totality;induction;member]allExA)as(existenceLaw&HExistenceLaw).
 pose proof(source_zfr_rec_attempts_exist M phi o a N totalG nonzero injective totality induction member allExA existenceLaw k
  BP BO BA BN HG HNZ HInj HT HI HM HAll HExistenceLaw)as PExistenceLaw.
 set(B:=([funlaw;totality;induction;member]++[chart;allExA])).
 assert(HB:source_rec_closure_carrier_inputs M phi o a N Y B).
 { exists[funlaw;totality;induction;member],chart,allExA. split;[reflexivity|]. split.
   - exists funlaw,totality,induction,member. split;[reflexivity|]. auto.
   - auto. }
 destruct(source_finite_telescope_total M(B++[nonzero])target)as(carrierLaw&HCarrierLaw).
 pose proof(source_zfr_rec_closure_carrier M phi o a N Y B nonzero target carrierLaw k BP BO BA BN BY HB HNZ HTarget HCarrierLaw)as PCarrierLaw.
 apply(source_zfr_finite_rule M[existenceLaw;carrierLaw]([funlaw;totalG;nonzero;injective;totality;induction;member]++[chart])target law k).
 - intros x HX. apply in_app_or in HX. destruct HX as[HX|[<-|[]]];[exact(Bounds x HX)|exact BChart].
 - exact BTarget.
 - exact HLaw.
 - intros x[<-|[<-|[]]];assumption.
 - intros cb cc cn BC Laws Premises.
   assert(PAll:source_full_prv M cb cc cn allExA).
   { apply(source_full_finite_telescope_apply M[totalG;nonzero;injective;totality;induction;member]allExA existenceLaw HExistenceLaw cb cc cn).
     - apply Laws. now left.
     - intros x HX. apply Premises. cbn in HX|-*. tauto. }
   apply(source_full_finite_telescope_apply M(B++[nonzero])target carrierLaw HCarrierLaw cb cc cn).
   + apply Laws. right. now left.
   + intros x HX. apply in_app_or in HX. destruct HX as[HX|[<-|[]]].
     * unfold B in HX. apply in_app_or in HX. destruct HX as[HX|[<-|[<-|[]]]].
       -- apply Premises. cbn in HX|-*. tauto.
       -- apply Premises. cbn. tauto.
       -- exact PAll.
     * apply Premises. cbn. tauto.
Qed.
Print Assumptions source_zfr_rec_closure_from_structure.
