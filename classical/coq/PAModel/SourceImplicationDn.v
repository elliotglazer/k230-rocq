(** Internally-many assignment closure of the actual implication law.
    All operation padding and point bounds are discharged from the named frame. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaPacking CodeExpressions SetFormulaCodes SourceBounded SourceBoundMonotone
 SourceNumeralLift FixedSourceBounds SourceImplicationFrame SourceImplicationPointBounds
 SourceImplicationDifferenceProgram SourceImplicationDifferenceUniversal SourceImplicationDifferencePoints SourceImplicationDifferenceLaw
 SourceRepresentationDifferenceProgram SourceRepresentationDifferencePoints SourceRepresentationPadding SourcePropositionalTemplates SourceFiniteTelescope
 SourceDn SourceDnPaddedTernaryMap SourceDescriptorProvability SourceDescriptorClosure.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
Unset Implicit Arguments.
Lemma implication_hole_bound M count hole :source_bounded M hole(succM M(succM M(succM M count))) ->
 source_bounded M hole(succM M(addM M count(code_numeral M 8))).
Proof.
 intro HB. apply(source_bounded_monotone M hole(succM M(succM M(succM M count)))
   (succM M(addM M count(code_numeral M 8))) HB).
 pose proof(coding_lt_add_left M count(code_numeral M 3)(code_numeral M 10)
   (proj2(fixed_source_numeral_lt_iff M 3 10)ltac:(lia)))as H.
 rewrite(Arithmetic.add_comm M count(code_numeral M 3)),(Arithmetic.add_comm M count(code_numeral M 10))in H.
 change(coding_lt M(addM M(code_numeral M 3)count)(addM M(code_numeral M 10)count))in H.
 cbn[code_numeral]in H. rewrite !Arithmetic.add_succ,Arithmetic.add_zero in H.
 rewrite(Arithmetic.add_comm M count(code_numeral M 8)).
 change(coding_lt M(succM M(succM M(succM M count)))
  (succM M(succM M(addM M(succM M(code_numeral M 7)) count)))).
 cbn[code_numeral]. rewrite !Arithmetic.add_succ,Arithmetic.add_zero. exact H.
Qed.

Theorem source_descriptor_canonical_implication_dn M T count left right guard coverage point1 point2 target repA rep1 rep2 repTarget:
 source_bounded M left(succM M(succM M(succM M count)))->source_bounded M right(succM M(succM M(succM M count)))->
 source_bounded M guard(succM M(succM M(succM M count)))->
 code_relation M(implication_point_environment M count left right guard)(E_implication_difference_all(SPTImpl(SPTSlot 6)(SPTSlot 7)))coverage->
 code_relation M(implication_point_environment M count left right guard)(E_implication_difference_all(SPTImpl(SPTSlot 6)(SPTIff(SPTSlot 0)(SPTSlot 4))))point1->
 code_relation M(implication_point_environment M count left right guard)(E_implication_difference_all(SPTImpl(SPTSlot 6)(SPTIff(SPTSlot 1)(SPTSlot 5))))point2->
 code_relation M(implication_point_environment M count left right guard)(E_implication_difference_all implication_difference_conclusion)target->
 source_dn M count coverage repA->source_dn M count point1 rep1->source_dn M count point2 rep2->source_dn M count target repTarget->
 exists operation1 operation2 condition inner body all result,
 code_relation M(implication_outer_environment M)E_double_difference_first_operation operation1/\
 code_relation M(implication_outer_environment M)E_implication_difference_second_operation operation2/\
 sf_relation M SFAnd operation1 operation2 condition/\sf_relation M SFImpl rep2 repTarget inner/\
 sf_relation M SFImpl rep1 inner body/\sf_relation M SFImpl repA body all/\sf_relation M SFImpl condition all result/\
 source_descriptor_provable M T result.
Proof.
 intros BL BR BG HC HP1 HP2 HT HDA HD1 HD2 HDT.
 destruct(implication_difference_conditions_total M count left right guard)
  as(op1&op2&condition&op1'&op2'&padded&HO1&HO2&HAnd&HO1'&HO2'&HAnd'&HPad&BCond&BPad).
 set(rho:=implication_point_environment M count left right guard).
 pose proof(implication_point_names_bound M count left right guard)as HNames.
 pose proof(implication_point_carrier_bound M count left right guard)as HCarrier.
 pose proof(implication_hole_bound M count left BL)as B4.
 pose proof(implication_hole_bound M count right BR)as B5.
 pose proof(implication_hole_bound M count guard BG)as B6.
 pose proof(implication_difference_all_expression_bound M rho(addM M count(code_numeral M 8))_ HNames HCarrier B4 B5 B6 coverage HC)as BC.
 pose proof(implication_difference_all_expression_bound M rho(addM M count(code_numeral M 8))_ HNames HCarrier B4 B5 B6 point1 HP1)as BP1.
 pose proof(implication_difference_all_expression_bound M rho(addM M count(code_numeral M 8))_ HNames HCarrier B4 B5 B6 point2 HP2)as BP2.
 pose proof(implication_difference_all_expression_bound M rho(addM M count(code_numeral M 8))_ HNames HCarrier B4 B5 B6 target HT)as BT.
 destruct(sf_relation_total M SFImpl point2 target)as(innerPoint&HIP).
 destruct(sf_relation_total M SFImpl point1 innerPoint)as(bodyPoint&HBP).
 destruct(sf_relation_total M SFImpl coverage bodyPoint)as(allPoint&HAP).
 destruct(sf_relation_total M SFImpl padded allPoint)as(pointProof&HPP).
 destruct(sf_relation_total M SFImpl rep2 repTarget)as(inner&HIR).
 destruct(sf_relation_total M SFImpl rep1 inner)as(body&HRB).
 destruct(sf_relation_total M SFImpl repA body)as(all&HRA).
 destruct(sf_relation_total M SFImpl condition all)as(result&HResult).
 assert(HTelescope:source_finite_telescope M[padded;coverage;point1;point2]target pointProof).
 { exists allPoint. split;[|exact HPP]. exists bodyPoint. split;[|exact HAP]. exists innerPoint. split;[|exact HBP].
   exists target. exact(conj eq_refl HIP). }
 pose proof(source_implication_difference_point_law_empty M rho(addM M count(code_numeral M 8))op1' op2' padded coverage point1 point2 target pointProof
  HNames HCarrier B4 B5 B6 BPad BC BP1 BP2 BT HO1' HO2' HC HP1 HP2 HT HAnd' HTelescope)as PPoint.
 exists op1,op2,condition,inner,body,all,result. refine(conj HO1(conj HO2(conj HAnd(conj HIR(conj HRB(conj HRA(conj HResult _))))))).
 exact(source_descriptor_dn_padded_ternary_map M T count condition padded coverage point1 point2 target repA rep1 rep2 repTarget
  innerPoint bodyPoint allPoint pointProof inner body all result(code_numeral M 6)
  BCond BC BP1 BP2 BT HPad HDA HD1 HD2 HDT HIP HBP HAP HPP HIR HRB HRA HResult
  (source_descriptor_provable_from_empty M T pointProof PPoint)).
Qed.
Print Assumptions source_descriptor_canonical_implication_dn.
