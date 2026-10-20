(** The implication point is a closed source theorem, obtained by actual
    finite implication rules. Its carrier premise is explicit in the law. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 SourceImplicationDifferencePoints SourceImplicationDifferenceUniversal SourceImplicationDifferenceProgram
 SourceRepresentationDifferencePoints SourceRepresentationDifferenceProgram SourcePropositionalTemplates
 SourceFiniteTelescope NumericalContexts NumericalSourceFull.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_implication_difference_point_law_empty M rho k operation1 operation2 condition coverage point1 point2 target law:
 (forall i,(i<4)%nat ->coding_lt M(rho i)k) ->coding_lt M(rho 7)k ->
 source_bounded M(rho 4)(succM M k) ->source_bounded M(rho 5)(succM M k) ->source_bounded M(rho 6)(succM M k) ->
 source_bounded M condition k ->source_bounded M coverage k ->source_bounded M point1 k ->
 source_bounded M point2 k ->source_bounded M target k ->
 code_relation M rho E_double_difference_first_operation operation1 ->
 code_relation M rho E_implication_difference_second_operation operation2 ->
 code_relation M rho(E_implication_difference_all(SPTImpl(SPTSlot 6)(SPTSlot 7)))coverage ->
 code_relation M rho(E_implication_difference_all(SPTImpl(SPTSlot 6)(SPTIff(SPTSlot 0)(SPTSlot 4))))point1 ->
 code_relation M rho(E_implication_difference_all(SPTImpl(SPTSlot 6)(SPTIff(SPTSlot 1)(SPTSlot 5))))point2 ->
 code_relation M rho(E_implication_difference_all implication_difference_conclusion)target ->
 sf_relation M SFAnd operation1 operation2 condition ->
 source_finite_telescope M[condition;coverage;point1;point2]target law ->
 source_full_prv M(zeroM M)(zeroM M)(zeroM M)law.
Proof.
 intros HNames HCarrier B4 B5 B6 BCond BCoverage BP1 BP2 BT HO1 HO2 HC HP1 HP2 HT HAnd HTelescope.
 destruct(proj1(source_bounded_accept_binary M SFAnd operation1 operation2 condition k(or_introl eq_refl)HAnd)BCond)as[BO1 BO2].
 apply(source_full_finite_telescope M[condition;coverage;point1;point2]target law k).
 - intros f[<-|[<-|[<-|[<-|[]]]]];assumption.
 - exact BT.
 - exact HTelescope.
 - apply context_bounded_empty.
 - intros cb cc cn HCtx Included Premises.
   pose proof(Premises condition(or_introl eq_refl))as PCond.
   pose proof(full_source_CE1 M cb cc cn operation1 operation2 condition(ex_intro _ k(conj BO1 HCtx))PCond HAnd)as PO1.
   pose proof(full_source_CE2 M cb cc cn operation1 operation2 condition(ex_intro _ k(conj BO2 HCtx))PCond HAnd)as PO2.
   exact(source_full_implication_difference_points M rho k cb cc cn operation1 operation2 coverage point1 point2 target
    HNames HCarrier B4 B5 B6 HCtx HO1 HO2 HC HP1 HP2 HT PO1 PO2
    (Premises coverage(or_intror(or_introl eq_refl)))
    (Premises point1(or_intror(or_intror(or_introl eq_refl))))
    (Premises point2(or_intror(or_intror(or_intror(or_introl eq_refl)))))).
Qed.
Print Assumptions source_implication_difference_point_law_empty.
