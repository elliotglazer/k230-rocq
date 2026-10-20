(** Curry the actual double-difference point proof into a pure source
    theorem. Its operation and representation hypotheses are discharged
    by real implication rules, rather than an assumed proof transformer. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 NumericalContexts NumericalEnvironments NumericalSourceFull SourceContextProofHelpers
 SourceRepresentationDifferenceProgram SourceRepresentationDifferencePoints SourcePropositionalTemplates.
Unset Implicit Arguments.
Theorem source_double_difference_point_law_empty M rho k operation1 operation2 condition point1 point2 target
 inner2 inner1 law :
 (forall i,(i<4)%nat ->coding_lt M(rho i) k) ->
 source_bounded M(rho 4)(succM M k) ->source_bounded M(rho 5)(succM M k) ->source_bounded M(rho 6)(succM M k) ->
 source_bounded M condition k ->source_bounded M point1 k ->source_bounded M point2 k ->source_bounded M target k ->
 code_relation M rho E_double_difference_first_operation operation1 ->
 code_relation M rho E_double_difference_second_operation operation2 ->
 code_relation M rho(E_double_difference_all(SPTImpl(SPTSlot 6)(SPTIff(SPTSlot 0)(SPTSlot 4)))) point1 ->
 code_relation M rho(E_double_difference_all(SPTImpl(SPTSlot 6)(SPTIff(SPTSlot 1)(SPTSlot 5)))) point2 ->
 code_relation M rho(E_double_difference_all double_difference_conclusion)target ->
 sf_relation M SFAnd operation1 operation2 condition ->sf_relation M SFImpl point2 target inner2 ->
 sf_relation M SFImpl point1 inner2 inner1 ->sf_relation M SFImpl condition inner1 law ->
 source_full_prv M(zeroM M)(zeroM M)(zeroM M) law.
Proof.
 intros HNames BX BY BG BCond BP1 BP2 BT HO1 HO2 HP1 HP2 HT HAnd HI2 HI1 HL.
 pose proof(proj1(source_bounded_accept_binary M SFAnd operation1 operation2 condition k(or_introl eq_refl) HAnd) BCond)as[BOp1 BOp2].
 pose proof(proj2(source_bounded_accept_binary M SFImpl point2 target inner2 k(or_intror(or_intror eq_refl)) HI2)(conj BP2 BT))as BI2.
 pose proof(proj2(source_bounded_accept_binary M SFImpl point1 inner2 inner1 k(or_intror(or_intror eq_refl)) HI1)(conj BP1 BI2))as BI1.
 pose proof(proj2(source_bounded_accept_binary M SFImpl condition inner1 law k(or_intror(or_intror eq_refl)) HL)(conj BCond BI1))as BL.
 destruct(environment_cons_total M(zeroM M)(zeroM M)(zeroM M) condition)as(b1&c1&n1&H1).
 assert(C1:context_bounded M b1 c1 n1 k).
 { apply(proj2(context_bounded_cons M _ _ _ condition b1 c1 n1 k H1)). split;[exact BCond|apply context_bounded_empty]. }
 destruct(environment_cons_total M b1 c1 n1 point1)as(b2&c2&n2&H2).
 assert(C2:context_bounded M b2 c2 n2 k).
 { exact(proj2(context_bounded_cons M b1 c1 n1 point1 b2 c2 n2 k H2)(conj BP1 C1)). }
 destruct(environment_cons_total M b2 c2 n2 point2)as(b3&c3&n3&H3).
 assert(C3:context_bounded M b3 c3 n3 k).
 { exact(proj2(context_bounded_cons M b2 c2 n2 point2 b3 c3 n3 k H3)(conj BP2 C2)). }
 pose proof(source_full_cons_head M(zeroM M)(zeroM M)(zeroM M)condition b1 c1 n1 k H1 BCond C1)as PC1.
 pose proof(source_full_cons_weaken M b1 c1 n1 point1 b2 c2 n2 k condition H2 C2 PC1)as PC2.
 pose proof(source_full_cons_weaken M b2 c2 n2 point2 b3 c3 n3 k condition H3 C3 PC2)as PC3.
 pose proof(full_source_CE1 M b3 c3 n3 operation1 operation2 condition(ex_intro _ k(conj BOp1 C3)) PC3 HAnd)as PO1.
 pose proof(full_source_CE2 M b3 c3 n3 operation1 operation2 condition(ex_intro _ k(conj BOp2 C3)) PC3 HAnd)as PO2.
 pose proof(source_full_cons_head M b1 c1 n1 point1 b2 c2 n2 k H2 BP1 C2)as PP12.
 pose proof(source_full_cons_weaken M b2 c2 n2 point2 b3 c3 n3 k point1 H3 C3 PP12)as PP13.
 pose proof(source_full_cons_head M b2 c2 n2 point2 b3 c3 n3 k H3 BP2 C3)as PP23.
 pose proof(source_full_double_difference_points M rho k b3 c3 n3 operation1 operation2 point1 point2 target
   HNames BX BY BG C3 HO1 HO2 HP1 HP2 HT PO1 PO2 PP13 PP23)as PT.
 pose proof(full_source_II M b2 c2 n2 point2 target inner2 b3 c3 n3(ex_intro _ k(conj BI2 C2)) PT H3 HI2)as PI2.
 pose proof(full_source_II M b1 c1 n1 point1 inner2 inner1 b2 c2 n2(ex_intro _ k(conj BI1 C1)) PI2 H2 HI1)as PI1.
 exact(full_source_II M(zeroM M)(zeroM M)(zeroM M) condition inner1 law b1 c1 n1
   (ex_intro _ k(conj BL(context_bounded_empty M _ _ k))) PI1 H1 HL).
Qed.
Print Assumptions source_double_difference_point_law_empty.

