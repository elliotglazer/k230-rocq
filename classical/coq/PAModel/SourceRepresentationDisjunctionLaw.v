(** Actual disjunction representation constructor for arbitrary internal source
    formulas. The pair/union conditions are literal antecedents, to be supplied
    by fixed operation-existence deductions in the witness construction. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes
 SourceBounded SourceRepresentationRecipe SourceRepresentationBinaryChildren SourceRepresentationConjunctionFrame
 SourcePairUnionDn SourcePairUnionFrame SourcePairUnionProgram SourceRepresentationDisjunctionPoint SourceRepresentationRecipeBounds SourceRepresentationPointCompatibility
 SourceRepresentationNamedRecipe SourceRepresentationNamedPoint SourceRepresentativeRenaming SourceDefinabilityBounds
 SourceFiniteCutoffShift SetSchemaConstructors SourceDescriptorProvability FixedSourceBounds
 SourceRepresentationDifferencePoints SourceRepresentationDifferenceProgram SourcePropositionalTemplates SourceZFRProvability.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Theorem source_representation_disjunction_law M count left right conjunction result :
 source_bounded M conjunction count ->sf_relation M SFOr left right conjunction ->
 source_representation_recipe M count conjunction result ->
 exists repLeft repRight namedLeft namedRight operation1 operation2 condition inner resultbody law,
 source_representation_recipe M count left repLeft /\source_representation_recipe M count right repRight /\
 source_representative_renaming M(code_numeral M 3)repLeft namedLeft /\
 source_representative_renaming M(code_numeral M 4)repRight namedRight /\
 code_relation M(conjunction_outer_environment M) E_pair_union_pair operation1 /\
 code_relation M(conjunction_outer_environment M) E_pair_union_union operation2 /\
 sf_relation M SFAnd operation1 operation2 condition /\
 sf_relation M SFImpl namedRight result inner /\sf_relation M SFImpl namedLeft inner resultbody /\
 sf_relation M SFImpl condition resultbody law /\source_zfr_provable M law.
Proof.
 intros HB HAnd HRecipe.
 pose proof(proj1(source_bounded_accept_binary M SFOr left right conjunction count(or_intror(or_introl eq_refl)) HAnd) HB)as[BL BR].
 destruct(source_representation_binary_children M count SFOr left right conjunction result (or_intror(or_introl eq_refl)) HAnd HRecipe)
  as(env&first&guard&ml&mr&rl&rr&rc&pl&pr&pc&repL&repR&HE&H1&H2&HML&HMR&HRL&HRR&HRelAnd&HPL&HPR&HPC&HDL&HDR&HDC&HLRecipe&HRRecipe).
 destruct(source_representative_renaming_total M(code_numeral M 3)repL)as(namedL&HNamedL).
 destruct(source_representative_renaming_total M(code_numeral M 4)repR)as(namedR&HNamedR).
 assert(N3:~coding_lt M(code_numeral M 3)(code_numeral M 2)).
 { intro H. apply(proj1(fixed_source_numeral_lt_iff M 3 2))in H. lia. }
 assert(N4:~coding_lt M(code_numeral M 4)(code_numeral M 2)).
 { intro H. apply(proj1(fixed_source_numeral_lt_iff M 4 2))in H. lia. }
 destruct(source_representation_point_reopen M count left env first guard ml rl pl repL(code_numeral M 3)namedL
  BL HE H1 H2 HML HRL HPL HDL N3 HNamedL)as(pointL&HPointL&HDNamedL).
 destruct(source_representation_point_reopen M count right env first guard mr rr pr repR(code_numeral M 4)namedR
  BR HE H1 H2 HMR HRR HPR HDR N4 HNamedR)as(pointR&HPointR&HDNamedR).
 set(rho:=conjunction_point_environment M count rl rr guard).
 assert(GLeft:code_relation M rho(E_double_difference_all(SPTImpl(SPTSlot 6)(SPTIff(SPTSlot 0)(SPTSlot 4))))pointL).
 { exact(proj2(representation_named_first_point M rho pointL) HPointL). }
 assert(GRight:code_relation M rho(E_double_difference_all(SPTImpl(SPTSlot 6)(SPTIff(SPTSlot 1)(SPTSlot 5))))pointR).
 { exact(proj2(representation_named_second_point M rho pointR) HPointR). }
 assert(GConj:code_relation M rho(E_double_difference_all pair_union_conclusion)pc).
 { apply(proj2(representation_named_disjunction_point M rho rc pc HRelAnd)).
   exact(proj1(representation_standard_point_graph M guard rc pc) HPC). }
 pose proof(source_representation_relative_bound M count left ml rl BL HML HRL)as BRL.
 pose proof(source_representation_relative_bound M count right mr rr BR HMR HRR)as BRR.
 pose proof(source_cutoff_shift_bounded M 1 env first count(source_envf_bound M count env HE) H1)as BF.
 pose proof(source_cutoff_shift_bounded M 1 first guard(succM M count) BF H2)as BG.
 destruct(source_zfr_canonical_pair_union_dn M count rl rr guard pointL pointR pc namedL namedR result
   BRL BRR BG GLeft GRight GConj HDNamedL HDNamedR HDC)
  as(op1&op2&condition&inner&resultbody&law&HO1&HO2&HCondition&HInner&HResultBody&HLaw&PLaw).
 exists repL,repR,namedL,namedR,op1,op2,condition,inner,resultbody,law.
 exact(conj HLRecipe(conj HRRecipe(conj HNamedL(conj HNamedR(conj HO1(conj HO2
  (conj HCondition(conj HInner(conj HResultBody(conj HLaw PLaw)))))))))).
Qed.
Print Assumptions source_representation_disjunction_law.

