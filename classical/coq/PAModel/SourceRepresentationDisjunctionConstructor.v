(** The named disjunction law obtained from the genuine representation
    recipe. All pair/union-operation and logical law proofs are supplied
    by checked constructors; none remains a proof premise here. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 SourceRepresentationRecipe SourceRepresentationDisjunctionLaw SourceRepresentationConjunctionFrame
 SourceRepresentationNamedDisjunction SourceNamedPairUnionFacts SourcePairUnionFrame SourceRepresentationConjunctionShell SourcePropositionalTemplates
 SourceRepresentativeRenaming SourceNamedQuantifierRules SourceDifferenceNumeralParameters SourceDifferenceProfile
 SourceRepresentationDifferencePoints SourceZFRProvability SourceSetTheoryDescriptors.
Unset Implicit Arguments.

Theorem source_zfr_named_disjunction_recipe M count left right conjunction result :
 source_bounded M conjunction count ->sf_relation M SFOr left right conjunction ->
 source_representation_recipe M count conjunction result ->
 exists repL repR namedL namedR matrixL matrixR matrixTarget exL exR exTarget out,
 source_representation_recipe M count left repL /\source_representation_recipe M count right repR /\
 source_representative_renaming M(code_numeral M 3)repL namedL /\
 source_representative_renaming M(code_numeral M 4)repR namedR /\
 sf_relation M SFAnd(RPU_member M 3)namedL matrixL /\
 sf_relation M SFAnd(RPU_member M 4)namedR matrixR /\
 sf_relation M SFAnd(RPU_member M 0)result matrixTarget /\
 source_named_quantifier M false(code_numeral M 3)matrixL exL /\
 source_named_quantifier M false(code_numeral M 4)matrixR exR /\
 source_named_quantifier M false(zeroM M)matrixTarget exTarget /\
 code_relation M(RPU_environment M namedL namedR result exTarget exL exR)
  (source_prop_expression RCS_result)out /\source_zfr_provable M out.
Proof.
 intros HBound HAnd HRecipe.
 destruct(proj1(source_bounded_accept_binary M SFOr left right conjunction count(or_intror(or_introl eq_refl))HAnd)HBound)as[BL BR].
 destruct(source_representation_disjunction_law M count left right conjunction result HBound HAnd HRecipe)
  as(repL&repR&namedL&namedR&op1&op2&condition&inner&body&law&HL&HR&HNL&HNR&HO1&HO2&HC&HI&HB&HLaw&PLaw).
 assert(E1:op1=RPU_operation1 M).
 { exact(code_relation_functional M E_pair_union_pair(conjunction_outer_environment M)op1(RPU_operation1 M)HO1(source_named_pair_operation_graph M)). }
 assert(E2:op2=RPU_operation2 M).
 { exact(code_relation_functional M E_pair_union_union(conjunction_outer_environment M)op2(RPU_operation2 M)HO2(source_named_union_operation_graph M)). }
 rewrite E1,E2 in HC.
 destruct(source_zfr_named_disjunction_from_point M repL repR namedL namedR result condition inner body law
  (source_representation_recipe_bounded M count left repL BL HL)
  (source_representation_recipe_bounded M count right repR BR HR)
  (source_representation_recipe_bounded M count conjunction result HBound HRecipe)
  HNL HNR HC HI HB HLaw PLaw)
  as(ml&mr&mt&el&er&et&out&HML&HMR&HMT&HEL&HER&HET&HOut&POut).
 exists repL,repR,namedL,namedR,ml,mr,mt,el,er,et,out.
 exact(conj HL(conj HR(conj HNL(conj HNR(conj HML(conj HMR(conj HMT
  (conj HEL(conj HER(conj HET(conj HOut POut))))))))))).
Qed.

Print Assumptions source_zfr_named_disjunction_recipe.
