(** Actual implication representation point from two literal Op2 laws.
    The assignment carrier covers the guard, so An minus (L minus R)
    represents implication there. No standard-code assumption is used. *)
From PAModel Require Import Model FiniteCoding CodeExpressions CodeExpressionPlug SetFormulaCodes SourceBounded
 SourcePropositionalTemplates SourceDifferenceProfile SourceRepresentationDifferencePoints SourceRepresentationDifferenceProgram
 SourceImplicationDifferenceProgram SourceImplicationDifferenceUniversal SourceImplicationDifferenceFull
 NumericalContexts NumericalSourceFull.
Unset Implicit Arguments.

Definition E_implication_difference_second_operation:=code_plug(difference_names(CEvar 7)(CEvar 2)(CEvar 3))
 source_difference_operation_expression.
Lemma implication_difference_first_profile_expression:
 E_implication_difference_all(SPTIff(SPTSlot 2)(SPTDifference(SPTSlot 0)(SPTSlot 1)))=
 code_plug(difference_names(CEvar 0)(CEvar 1)(CEvar 2))source_difference_profile_expression.
Proof. reflexivity. Qed.
Lemma implication_difference_second_profile_expression:
 E_implication_difference_all(SPTIff(SPTSlot 3)(SPTDifference(SPTSlot 7)(SPTSlot 2)))=
 code_plug(difference_names(CEvar 7)(CEvar 2)(CEvar 3))source_difference_profile_expression.
Proof. reflexivity. Qed.

Theorem source_full_implication_difference_points M rho k b c n operation1 operation2 coverage point1 point2 target:
 (forall i,(i<4)%nat ->coding_lt M(rho i)k) ->coding_lt M(rho 7)k ->
 source_bounded M(rho 4)(succM M k) ->source_bounded M(rho 5)(succM M k) ->source_bounded M(rho 6)(succM M k) ->
 context_bounded M b c n k ->
 code_relation M rho E_double_difference_first_operation operation1 ->
 code_relation M rho E_implication_difference_second_operation operation2 ->
 code_relation M rho(E_implication_difference_all(SPTImpl(SPTSlot 6)(SPTSlot 7)))coverage ->
 code_relation M rho(E_implication_difference_all(SPTImpl(SPTSlot 6)(SPTIff(SPTSlot 0)(SPTSlot 4))))point1 ->
 code_relation M rho(E_implication_difference_all(SPTImpl(SPTSlot 6)(SPTIff(SPTSlot 1)(SPTSlot 5))))point2 ->
 code_relation M rho(E_implication_difference_all implication_difference_conclusion)target ->
 source_full_prv M b c n operation1 ->source_full_prv M b c n operation2 ->source_full_prv M b c n coverage ->
 source_full_prv M b c n point1 ->source_full_prv M b c n point2 ->source_full_prv M b c n target.
Proof.
 intros HNames HCarrier B4 B5 B6 HCtx HOp1 HOp2 HCoverage HP1 HP2 HT POp1 POp2 PCoverage PP1 PP2.
 destruct(code_relation_total M(E_implication_difference_all(SPTIff(SPTSlot 2)(SPTDifference(SPTSlot 0)(SPTSlot 1))))rho)as(profile1&HProfile1).
 destruct(code_relation_total M(E_implication_difference_all(SPTIff(SPTSlot 3)(SPTDifference(SPTSlot 7)(SPTSlot 2))))rho)as(profile2&HProfile2).
 assert(HParam1:forall i,code_relation M rho(difference_names(CEvar 0)(CEvar 1)(CEvar 2)i)(difference_values M(rho 0)(rho 1)(rho 2)i))
  by(intros[|[|[|i]]];reflexivity).
 assert(HParam2:forall i,code_relation M rho(difference_names(CEvar 7)(CEvar 2)(CEvar 3)i)(difference_values M(rho 7)(rho 2)(rho 3)i))
  by(intros[|[|[|i]]];reflexivity).
 assert(PProfile1:source_full_prv M b c n profile1).
 { apply(source_full_difference_profile M b c n(difference_values M(rho 0)(rho 1)(rho 2))operation1 profile1).
   - apply(proj1(code_relation_plug M rho(difference_values M(rho 0)(rho 1)(rho 2))
      (difference_names(CEvar 0)(CEvar 1)(CEvar 2))source_difference_operation_expression operation1 HParam1));exact HOp1.
   - rewrite implication_difference_first_profile_expression in HProfile1.
     apply(proj1(code_relation_plug M rho(difference_values M(rho 0)(rho 1)(rho 2))
      (difference_names(CEvar 0)(CEvar 1)(CEvar 2))source_difference_profile_expression profile1 HParam1));exact HProfile1.
   - exact POp1. }
 assert(PProfile2:source_full_prv M b c n profile2).
 { apply(source_full_difference_profile M b c n(difference_values M(rho 7)(rho 2)(rho 3))operation2 profile2).
   - apply(proj1(code_relation_plug M rho(difference_values M(rho 7)(rho 2)(rho 3))
      (difference_names(CEvar 7)(CEvar 2)(CEvar 3))source_difference_operation_expression operation2 HParam2));exact HOp2.
   - rewrite implication_difference_second_profile_expression in HProfile2.
     apply(proj1(code_relation_plug M rho(difference_values M(rho 7)(rho 2)(rho 3))
      (difference_names(CEvar 7)(CEvar 2)(CEvar 3))source_difference_profile_expression profile2 HParam2));exact HProfile2.
   - exact POp2. }
 exact(source_full_implication_difference_universal M rho k b c n profile1 profile2 coverage point1 point2 target
  HNames HCarrier B4 B5 B6 HCtx HProfile1 HProfile2 HCoverage HP1 HP2 HT PProfile1 PProfile2 PCoverage PP1 PP2).
Qed.
Print Assumptions source_full_implication_difference_points.
