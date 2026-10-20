(** Automatic hygienic bounds and Op2 syntax for the full Dn conjunction
    law. No source proof, reflection fact, or mathematical axiom image is
    a premise of this logical theorem. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaPacking CodeExpressions
 SetFormulaCodes SourceBounded SourceBoundMonotone FixedSourceBounds
 SourceRepresentationDifferenceProgram SourceRepresentationDifferencePoints SourceRepresentationPointBounds
 SourceRepresentationConjunctionFrame SourceRepresentationDifferenceDn SourcePropositionalTemplates
 SourceDescriptorProvability SourceDn.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Lemma conjunction_hole_bound M count hole :source_bounded M hole(succM M(succM M(succM M count))) ->
 source_bounded M hole(succM M(addM M count(code_numeral M 6))).
Proof.
 intro HB. apply(source_bounded_monotone M hole(succM M(succM M(succM M count)))
   (succM M(addM M count(code_numeral M 6))) HB).
 pose proof(coding_lt_add_left M count(code_numeral M 3)(code_numeral M 8)
   (proj2(fixed_source_numeral_lt_iff M 3 8)ltac:(lia)))as H.
 rewrite(Arithmetic.add_comm M count(code_numeral M 3)),(Arithmetic.add_comm M count(code_numeral M 8))in H.
 change(coding_lt M(addM M(succM M(succM M(succM M(zeroM M)))) count)
  (addM M(succM M(succM M(succM M(succM M(succM M(succM M(succM M(succM M(zeroM M))))))))) count))in H.
 rewrite !Arithmetic.add_succ,Arithmetic.add_zero in H.
 rewrite(Arithmetic.add_comm M count(code_numeral M 6)).
 change(coding_lt M(succM M(succM M(succM M count)))
  (succM M(succM M(addM M(succM M(code_numeral M 5)) count)))).
 cbn[code_numeral]. rewrite !Arithmetic.add_succ,Arithmetic.add_zero. exact H.
Qed.
Theorem source_descriptor_canonical_conjunction_dn M T count left right guard point1 point2 target rep1 rep2 repTarget :
 source_bounded M left(succM M(succM M(succM M count))) ->
 source_bounded M right(succM M(succM M(succM M count))) ->
 source_bounded M guard(succM M(succM M(succM M count))) ->
 code_relation M(conjunction_point_environment M count left right guard)
  (E_double_difference_all(SPTImpl(SPTSlot 6)(SPTIff(SPTSlot 0)(SPTSlot 4))))point1 ->
 code_relation M(conjunction_point_environment M count left right guard)
  (E_double_difference_all(SPTImpl(SPTSlot 6)(SPTIff(SPTSlot 1)(SPTSlot 5))))point2 ->
 code_relation M(conjunction_point_environment M count left right guard)
  (E_double_difference_all double_difference_conclusion)target ->
 source_dn M count point1 rep1 ->source_dn M count point2 rep2 ->source_dn M count target repTarget ->
 exists operation1 operation2 condition inner resultbody result,
 code_relation M(conjunction_outer_environment M) E_double_difference_first_operation operation1 /\
 code_relation M(conjunction_outer_environment M) E_double_difference_second_operation operation2 /\
 sf_relation M SFAnd operation1 operation2 condition /\
 sf_relation M SFImpl rep2 repTarget inner /\sf_relation M SFImpl rep1 inner resultbody /\
 sf_relation M SFImpl condition resultbody result /\source_descriptor_provable M T result.
Proof.
 intros BL BR BG HP1 HP2 HT HD1 HD2 HDT.
 destruct(conjunction_difference_conditions_total M count left right guard)
   as(op1&op2&condition&op1'&op2'&padded&HO1&HO2&HAnd&HO1'&HO2'&HAnd'&HPad&BCond&BPad).
 set(rho:=conjunction_point_environment M count left right guard).
 assert(HNames:forall i,(i<4)%nat ->coding_lt M(rho i)(addM M count(code_numeral M 6))).
 { exact(conjunction_point_names_bound M count left right guard). }
 pose proof(conjunction_hole_bound M count left BL)as B4.
 pose proof(conjunction_hole_bound M count right BR)as B5.
 pose proof(conjunction_hole_bound M count guard BG)as B6.
 assert(BP1:source_bounded M point1(addM M count(code_numeral M 6))).
 { exact(double_difference_all_expression_bound M rho(addM M count(code_numeral M 6)) _ HNames B4 B5 B6 point1 HP1). }
 assert(BP2:source_bounded M point2(addM M count(code_numeral M 6))).
 { exact(double_difference_all_expression_bound M rho(addM M count(code_numeral M 6)) _ HNames B4 B5 B6 point2 HP2). }
 assert(BT:source_bounded M target(addM M count(code_numeral M 6))).
 { exact(double_difference_all_expression_bound M rho(addM M count(code_numeral M 6)) _ HNames B4 B5 B6 target HT). }
 destruct(sf_relation_total M SFImpl point2 target)as(innerPoint&HIP).
 destruct(sf_relation_total M SFImpl point1 innerPoint)as(pointLaw&HPL).
 destruct(sf_relation_total M SFImpl padded pointLaw)as(pointProof&HPP).
 destruct(sf_relation_total M SFImpl rep2 repTarget)as(inner&HIR).
 destruct(sf_relation_total M SFImpl rep1 inner)as(resultbody&HRB).
 destruct(sf_relation_total M SFImpl condition resultbody)as(result&HResult).
 exists op1,op2,condition,inner,resultbody,result.
 refine(conj HO1(conj HO2(conj HAnd(conj HIR(conj HRB(conj HResult _)))))).
 exact(source_descriptor_double_difference_dn M T count rho(code_numeral M 4)op1' op2' condition padded
   point1 point2 target rep1 rep2 repTarget innerPoint pointLaw pointProof inner resultbody result
   HNames B4 B5 B6 BCond BPad BP1 BP2 BT HPad HO1' HO2' HP1 HP2 HT HAnd'
   HIP HPL HPP HD1 HD2 HDT HIR HRB HResult).
Qed.
Print Assumptions conjunction_hole_bound.
Print Assumptions source_descriptor_canonical_conjunction_dn.

