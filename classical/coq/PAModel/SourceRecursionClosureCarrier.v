(** The genuine RR carrier contains the initial value and is closed under G. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded NumericalContexts NumericalSourceFull
 SourceFiniteTelescope SourceZFRFiniteRule SourceRecursionStructureGraphs SourceRecursionStructureBounds SourceRecursionRangeBackground
 SourceRecursionRangeBase SourceRecursionClosureCarrierInputs SourceRecursionValuesClosed SourceRecursionClosureSyntax SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_rec_closure_carrier M phi o a N Y A nonzero target law k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M Y k ->
 source_rec_closure_carrier_inputs M phi o a N Y A ->source_rec_nonzero M o N nonzero ->source_rec_closure M phi a Y target ->
 source_finite_telescope M(A++[nonzero])target law ->source_zfr_provable M law.
Proof.
 intros BP BO BA BN BY HA HNZ HT HLaw.
 pose proof(source_rec_closure_carrier_inputs_bounded M phi o a N Y A k BP BO BA BN BY HA)as Bounds.
 pose proof(source_rec_nonzero_bounded M o N nonzero k BO BN HNZ)as BNZ.
 pose proof(source_rec_closure_bounded M phi a Y target k BP BA BY HT)as BTarget.
 destruct HT as(initial&guard&binary&member&body&ex&point&all&HI&HG&HB&HM&HBody&HEx&HP&HAll&HAnd).
 assert(HClosed:source_rec_values_closed M phi Y all).
 { exists guard,ex,point. split;[exact HG|]. split;[exists binary,member,body;auto|auto]. }
 destruct(source_finite_telescope_total M A all)as(closedLaw&HClosedLaw).
 pose proof(source_zfr_rec_range_closed M phi o a N Y A all closedLaw k BP BO BA BN BY HA HClosed HClosedLaw)as PClosedLaw.
 destruct HA as(background&chart&allExA&E&HBack&HChart&HAllExA). subst A.
 destruct HBack as(funlaw&totality&induction&initialMember&EBack&HFun&HTot&HInd&HInitial). subst background.
 destruct(source_finite_telescope_total M[nonzero;initialMember;chart]initial)as(baseLaw&HBaseLaw).
 pose proof(source_zfr_rec_range_base M phi o a N Y nonzero initialMember chart initial baseLaw k BP BO BA BN BY HNZ HInitial HChart HI HBaseLaw)as PBaseLaw.
 apply(source_zfr_finite_rule M[baseLaw;closedLaw](([funlaw;totality;induction;initialMember]++[chart;allExA])++[nonzero])target law k).
 - intros x HX. apply in_app_or in HX. destruct HX as[HX|[<-|[]]];[exact(Bounds x HX)|exact BNZ].
 - exact BTarget.
 - exact HLaw.
 - intros x[<-|[<-|[]]];assumption.
 - intros cb cc cn BC Laws Premises.
   assert(PI:source_full_prv M cb cc cn initial).
   { apply(source_full_finite_telescope_apply M[nonzero;initialMember;chart]initial baseLaw HBaseLaw cb cc cn).
     - apply Laws. now left.
     - intros x HX. apply Premises. rewrite !in_app_iff. cbn in HX|-*. tauto. }
   assert(PC:source_full_prv M cb cc cn all).
   { apply(source_full_finite_telescope_apply M([funlaw;totality;induction;initialMember]++[chart;allExA])all closedLaw HClosedLaw cb cc cn).
     - apply Laws. right. now left.
     - intros x HX. apply Premises,in_or_app. now left. }
   exact(full_source_CI M cb cc cn initial all target(ex_intro _ k(conj BTarget BC))PI PC HAnd).
Qed.
Print Assumptions source_zfr_rec_closure_carrier.
