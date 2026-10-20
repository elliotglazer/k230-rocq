(** Actual two-witness uniqueness step for arbitrary internal unary matrices. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourceBoundMonotone
 NumericalRenaming SourceQuantifierRules SourceImplicationAllShift SourceDefinabilityStep
 SourceDefinabilityPrimitives SourceNumFUniqueRecipe SourceNumFUniqueSyntax SourceNumFUniquePrograms
 SourceNumFUniqueFiniteShells SourceNumFUniqueBounds SourceNumFClosureBounds SourceNumFClosurePrograms
 SourceNumFClosureFiniteShells SourcePropositionalTemplates SourceWitnessProofComposition SourceZFRProvability.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Local Opaque source_def_successor01 numf_successor02 numf_successor03 numf_closure_succ_shift_form.
Ltac nu_graph :=lazymatch goal with
 | |-code_relation ?M ?rho(source_prop_expression(SPTSlot ?idx))?out=>reflexivity
 | |-code_relation ?M ?rho(source_prop_expression(SPTImpl ?A ?B))?out=>
  match goal with H:sf_relation M SFImpl ?a ?b out|-_=>apply(source_prop_template_join M rho SFImpl A B a b out);[nu_graph|nu_graph|exact H]end
 | |-code_relation ?M ?rho(source_prop_expression(SPTAnd ?A ?B))?out=>
  match goal with H:sf_relation M SFAnd ?a ?b out|-_=>apply(source_prop_template_join M rho SFAnd A B a b out);[nu_graph|nu_graph|exact H]end
 end.
Theorem source_zfr_numf_unique_step M p q old result :source_bounded M p(code_numeral M 1) ->
 source_def_step M false p q ->source_numf_unique_recipe M p old ->source_numf_unique_recipe M q result ->
 source_zfr_provable M old ->source_zfr_provable M result.
Proof.
 intros BP HStep HOld HResult POld.
 destruct(source_numf_unique_recipe_parts M p old HOld)as(ps&oldInner&HPS&HOldInner&HOldOut).
 destruct(source_numf_unique_recipe_parts M q result HResult)as(qs&newInner&HQS&HNewInner&HNewOut).
 destruct(source_numf_step_comparison_structure M p q BP HStep)as(ps'&pair&shifted&pair2&pair3&q1&q2&
  HPS'&HPair&HQ&HPairShifted&HPairShift&HPair2&HQ1&HQShift&HPair3&HQ2&HQ1Shift).
 assert(E:ps'=ps)by(eapply numerical_renaming_functional;eassumption). subst ps'.
 assert(E:qs=q1)by(eapply numerical_renaming_functional;eassumption). subst qs.
 pose proof(source_def_numeral_step_bound M p q BP HStep)as BQ.
 pose proof(source_shift_bound M p ps(code_numeral M 1)BP HPS)as BPS.
 pose proof(source_shift_bound M q q1(code_numeral M 1)BQ HQShift)as BQ1.
 pose proof(source_shift_bound M q1 q2(code_numeral M 2)BQ1 HQ1Shift)as BQ2.
 pose proof(source_numf_bound_to_six M p 1 ltac:(lia)BP)as BP6.
 pose proof(source_numf_bound_to_six M ps 2 ltac:(lia)BPS)as BPS6.
 pose proof(source_numf_bound_to_six M q 1 ltac:(lia)BQ)as BQ6.
 pose proof(source_numf_bound_to_six M q1 2 ltac:(lia)BQ1)as BQ16.
 pose proof(source_numf_bound_to_six M q2 3 ltac:(lia)BQ2)as BQ26.
 destruct(source_numf_compare_successor_bounds M)as(BS12&BS03).
 pose proof(source_numf_bound_to_six M _ 3 ltac:(lia)BS12)as BS126.
 pose proof(source_numf_bound_to_six M _ 4 ltac:(lia)BS03)as BS036.
 pose proof(source_numf_bound_to_six M _ 2 ltac:(lia)(numerical_def_successor_bound M))as BS016.
 pose proof(source_numf_equal_bound6 M 0 1 ltac:(lia)ltac:(lia))as BE01.
 pose proof(source_numf_equal_bound6 M 1 2 ltac:(lia)ltac:(lia))as BE12.
 pose proof(source_numf_equal_bound6 M 2 3 ltac:(lia)ltac:(lia))as BE23.
 assert(BPair:source_bounded M pair(code_numeral M 6)).
 { exact(proj2(source_bounded_accept_binary M SFAnd p _ pair(code_numeral M 6)(or_introl eq_refl)HPair)(conj BP6 BS016)). }
 destruct(source_numf_unique_square_shell M)as(tail&middle&fixed&HFixedTail&HFixedMiddle&HFixed&PFixed).
 destruct(sf_relation_total M SFImpl pair(numf_equal_code M 1 2))as(targetA&HTargetA).
 destruct(sf_relation_total M SFImpl shifted(numf_equal_code M 2 3))as(shiftA&HShiftA).
 pose proof(source_implication_shift_graph M pair _ targetA shifted _ shiftA HTargetA HShiftA HPairShift(source_numf_equal_shift M 1 2))as HTAShift.
 destruct(sf_relation_total M SFImpl pair3 shiftA)as(point&HPoint).
 set(env:=fun idx:nat=>match idx with 0=>p|1=>ps|2=>numf_equal01 M|3=>numf_closure_succ_shift_code M|
  4=>code_numeral M(sf_encode numf_successor03)|_=>numf_equal_code M 2 3 end).
 assert(PPoint:source_zfr_provable M point).
 { apply(source_zfr_prop_two M nu_old nu_fixed nu_result source_numf_unique_point_program env(code_numeral M 6)old fixed point).
   - intros[|[|[|[|[|idx]]]]];cbn[env];assumption.
   - unfold nu_old. nu_graph.
   - unfold nu_fixed. nu_graph.
   - unfold nu_result. nu_graph.
   - exact POld.
   - exact PFixed. }
 assert(BTargetA:source_bounded M targetA(code_numeral M 6)).
 { exact(proj2(source_bounded_accept_binary M SFImpl pair _ targetA(code_numeral M 6)(or_intror(or_intror eq_refl))HTargetA)(conj BPair BE12)). }
 destruct(sf_relation_total M SFImpl q2 targetA)as(map2&HMap2).
 pose proof(source_zfr_exists_implication M pair3 q2 targetA shiftA point map2(code_numeral M 6)(code_numeral M 6)
  BQ26 BTargetA HQ2 HTAShift HPoint HMap2 PPoint)as PMap2.
 destruct(sf_relation_total M SFImpl q2(numf_equal_code M 1 2))as(shiftInner&HShiftInner).
 destruct(sf_relation_total M SFImpl pair shiftInner)as(firstPoint&HFirstPoint).
 set(swapenv:=fun idx:nat=>match idx with 0=>q2|1=>pair|_=>numf_equal_code M 1 2 end).
 assert(PFirstPoint:source_zfr_provable M firstPoint).
 { apply(source_zfr_prop_one M _ _ source_numf_closure_reverse_point_program swapenv(code_numeral M 6)map2 firstPoint).
   - intros[|[|idx]];cbn[swapenv];assumption.
   - nu_graph.
   - nu_graph.
   - exact PMap2. }
 pose proof(source_implication_shift_graph M q1 _ newInner q2 _ shiftInner HNewInner HShiftInner HQ1Shift(source_numf_equal_shift M 0 1))as HInnerShift.
 assert(BInner:source_bounded M newInner(code_numeral M 6)).
 { exact(proj2(source_bounded_accept_binary M SFImpl q1 _ newInner(code_numeral M 6)(or_intror(or_intror eq_refl))HNewInner)(conj BQ16 BE01)). }
 exact(source_zfr_exists_implication M pair q newInner shiftInner firstPoint result(code_numeral M 6)(code_numeral M 6)
  BQ6 BInner HQ HInnerShift HFirstPoint HNewOut PFirstPoint).
Qed.
Print Assumptions source_zfr_numf_unique_step.
