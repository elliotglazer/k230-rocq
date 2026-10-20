(** Combine two actual Op2 certificates and two quantified representation
    points. This is the logical conjunction step, with arbitrary coded
    matrix holes and an unchanged internally coded source context. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions CodeExpressionPlug
 SetFormulaCodes SetSchemaConstructors SchemaConstructorBounds SourceBounded SourceDifferenceProfile
 SourcePropositionalTemplates SourceRepresentationDifferenceProgram SourceUniversalPrograms
 SourceFiniteParameters SourceFiniteParameterProofs NumericalContexts NumericalSourceFull.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition representation_member_expression name :=E_sf SFMember(CEconst 0)(CEadd name(CEconst 1)).
Definition double_difference_point_plug i :=match i with
 |0=>representation_member_expression(CEvar 0)|1=>representation_member_expression(CEvar 1)
 |2=>representation_member_expression(CEvar 2)|3=>representation_member_expression(CEvar 3)
 |4=>CEvar 4|5=>CEvar 5|_=>CEvar 6 end.
Definition E_double_difference_all p :=E_sf SFAll
 (code_plug double_difference_point_plug(source_prop_expression p))(CEconst 0).
Definition difference_names x y r i :=match i with 0=>x|1=>y|2=>r|_=>CEconst i end.
Definition difference_values M x y r i :=match i with 0=>x|1=>y|2=>r|_=>code_numeral M i end.
Definition E_double_difference_first_operation :=code_plug(difference_names(CEvar 0)(CEvar 1)(CEvar 2))
 source_difference_operation_expression.
Definition E_double_difference_second_operation :=code_plug(difference_names(CEvar 0)(CEvar 2)(CEvar 3))
 source_difference_operation_expression.
Lemma double_difference_first_profile_expression :
 E_double_difference_all(SPTIff(SPTSlot 2)(SPTDifference(SPTSlot 0)(SPTSlot 1)))=
 code_plug(difference_names(CEvar 0)(CEvar 1)(CEvar 2))source_difference_profile_expression.
Proof. reflexivity. Qed.
Lemma double_difference_second_profile_expression :
 E_double_difference_all(SPTIff(SPTSlot 3)(SPTDifference(SPTSlot 0)(SPTSlot 2)))=
 code_plug(difference_names(CEvar 0)(CEvar 2)(CEvar 3))source_difference_profile_expression.
Proof. reflexivity. Qed.
Definition double_difference_point_values {A}(a b c d x y g:A) i :=match i with
 |0=>a|1=>b|2=>c|3=>d|4=>x|5=>y|_=>g end.
Theorem source_full_double_difference_points M rho k b c n operation1 operation2 point1 point2 target :
 (forall i,(i<4)%nat ->coding_lt M(rho i) k) ->
 source_bounded M(rho 4)(succM M k) ->source_bounded M(rho 5)(succM M k) ->
 source_bounded M(rho 6)(succM M k) ->context_bounded M b c n k ->
 code_relation M rho E_double_difference_first_operation operation1 ->
 code_relation M rho E_double_difference_second_operation operation2 ->
 code_relation M rho(E_double_difference_all(SPTImpl(SPTSlot 6)(SPTIff(SPTSlot 0)(SPTSlot 4)))) point1 ->
 code_relation M rho(E_double_difference_all(SPTImpl(SPTSlot 6)(SPTIff(SPTSlot 1)(SPTSlot 5)))) point2 ->
 code_relation M rho(E_double_difference_all double_difference_conclusion) target ->
 source_full_prv M b c n operation1 ->source_full_prv M b c n operation2 ->
 source_full_prv M b c n point1 ->source_full_prv M b c n point2 ->source_full_prv M b c n target.
Proof.
 intros HNames BX BY BG HC HOp1 HOp2 HP1 HP2 HT POp1 POp2 PP1 PP2.
 destruct(code_relation_total M(representation_member_expression(CEvar 0))rho)as(a&HA).
 destruct(code_relation_total M(representation_member_expression(CEvar 1))rho)as(d&HD).
 destruct(code_relation_total M(representation_member_expression(CEvar 2))rho)as(e&HE).
 destruct(code_relation_total M(representation_member_expression(CEvar 3))rho)as(f&HF).
 set(values:=double_difference_point_values a d e f(rho 4)(rho 5)(rho 6)).
 assert(HValues:forall i,code_relation M rho(double_difference_point_plug i)(values i)).
 { intros[|[|[|[|[|[|i]]]]]];cbn[double_difference_point_plug values double_difference_point_values];try assumption;reflexivity. }
 assert(BValues:forall i,source_bounded M(values i)(succM M k)).
 { assert(BAtom:forall i z,(i<4)%nat ->code_relation M rho(representation_member_expression(CEvar i))z ->source_bounded M z(succM M k)).
   { intros i z HI HZ.
     assert(HIndex:code_relation M rho(CEadd(CEvar i)(CEconst 1))(succM M(rho i))).
     { exists(rho i),(code_numeral M 1). split;[reflexivity|]. split;[reflexivity|apply Arithmetic.succ_as_add]. }
     apply(proj2(source_bounded_accept_atom M SFMember(zeroM M)(succM M(rho i)) z(succM M k)
       (or_introl eq_refl)(proj1(schema_expression_graph M rho SFMember(CEconst 0)(CEadd(CEvar i)(CEconst 1))
        (zeroM M)(succM M(rho i)) z eq_refl HIndex) HZ))).
     split;[apply coding_zero_lt_succ|apply coding_lt_succ_cancel,HNames;exact HI]. }
   intros[|[|[|[|[|[|i]]]]]];cbn[values double_difference_point_values];try assumption;
    eapply BAtom;try eassumption;auto. }
 destruct(code_relation_total M(E_double_difference_all(SPTIff(SPTSlot 2)(SPTDifference(SPTSlot 0)(SPTSlot 1))))rho)as(profile1&HProfile1).
 destruct(code_relation_total M(E_double_difference_all(SPTIff(SPTSlot 3)(SPTDifference(SPTSlot 0)(SPTSlot 2))))rho)as(profile2&HProfile2).
 assert(HParam1:forall i,code_relation M rho(difference_names(CEvar 0)(CEvar 1)(CEvar 2)i)(difference_values M(rho 0)(rho 1)(rho 2)i))
   by(intros[|[|[|i]]];reflexivity).
 assert(HParam2:forall i,code_relation M rho(difference_names(CEvar 0)(CEvar 2)(CEvar 3)i)(difference_values M(rho 0)(rho 2)(rho 3)i))
   by(intros[|[|[|i]]];reflexivity).
 assert(PProfile1:source_full_prv M b c n profile1).
 { apply(source_full_difference_profile M b c n(difference_values M(rho 0)(rho 1)(rho 2)) operation1 profile1).
   - apply(proj1(code_relation_plug M rho(difference_values M(rho 0)(rho 1)(rho 2))
      (difference_names(CEvar 0)(CEvar 1)(CEvar 2))source_difference_operation_expression operation1 HParam1));exact HOp1.
   - rewrite double_difference_first_profile_expression in HProfile1.
     apply(proj1(code_relation_plug M rho(difference_values M(rho 0)(rho 1)(rho 2))
      (difference_names(CEvar 0)(CEvar 1)(CEvar 2))source_difference_profile_expression profile1 HParam1));exact HProfile1.
   - exact POp1. }
 assert(PProfile2:source_full_prv M b c n profile2).
 { apply(source_full_difference_profile M b c n(difference_values M(rho 0)(rho 2)(rho 3)) operation2 profile2).
   - apply(proj1(code_relation_plug M rho(difference_values M(rho 0)(rho 2)(rho 3))
      (difference_names(CEvar 0)(CEvar 2)(CEvar 3))source_difference_operation_expression operation2 HParam2));exact HOp2.
   - rewrite double_difference_second_profile_expression in HProfile2.
     apply(proj1(code_relation_plug M rho(difference_values M(rho 0)(rho 2)(rho 3))
      (difference_names(CEvar 0)(CEvar 2)(CEvar 3))source_difference_profile_expression profile2 HParam2));exact HProfile2.
   - exact POp2. }
 destruct(code_relation_total M(source_prop_expression double_difference_conclusion)values)as(body&HBody).
 assert(HBodyGraph:code_relation M rho(code_plug double_difference_point_plug(source_prop_expression double_difference_conclusion))body).
 { exact(proj2(code_relation_plug M rho values double_difference_point_plug
   (source_prop_expression double_difference_conclusion) body HValues) HBody). }
 pose proof(proj1(schema_expression_graph M rho SFAll _ (CEconst 0) body(zeroM M) target HBodyGraph eq_refl) HT)as HAll.
 apply(source_full_double_difference_representation M values k b c n body target BValues HC);[|exact HBody|exact HAll].
 intros p HIn v all HV HVA.
 assert(HVGraph:code_relation M rho(code_plug double_difference_point_plug(source_prop_expression p))v).
 { exact(proj2(code_relation_plug M rho values double_difference_point_plug(source_prop_expression p)v HValues) HV). }
 assert(HAllGraph:code_relation M rho(E_double_difference_all p)all).
 { exact(proj2(schema_expression_graph M rho SFAll _ (CEconst 0) v(zeroM M) all HVGraph eq_refl) HVA). }
 destruct HIn as[<-|[<-|[<-|[<-|[]]]]].
 - rewrite(code_relation_functional M _ rho all profile1 HAllGraph HProfile1). exact PProfile1.
 - rewrite(code_relation_functional M _ rho all profile2 HAllGraph HProfile2). exact PProfile2.
 - rewrite(code_relation_functional M _ rho all point1 HAllGraph HP1). exact PP1.
 - rewrite(code_relation_functional M _ rho all point2 HAllGraph HP2). exact PP2.
Qed.
Print Assumptions source_full_double_difference_points.


