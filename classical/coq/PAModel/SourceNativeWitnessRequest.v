(** Two actual instances of one ordinary reflection theorem give the
 native witness request. The output-universal reflection is constructed
 internally from Refl/LL and ordinary carrier-membership proofs. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 SourceRelativization SourceRelativizationBounds SourceSetRelativization SourceSetRelativizationBounds
 SourceOrdinaryReflectionSyntax SourceOrdinaryReflectionSubstitution SourceHierarchySyntax
 SourceWitnessThetaInstances SourceWitnessPointReflection SourceSubstitutionBounds NumericalSubstitutionMaps NumericalSubstitution
 SourceRelativizedSelectors SourceReflectionSelectors SourceReflectedExistential SourcePropositionalTemplates SourcePropositionalRebase
 SourceReflectedRequestLink SourceIffGraphs NumericalContexts NumericalSourceFull SourceDerivedRules SourceQuantifierRules
 NumericalRenaming NumericalContextRenaming SourceZFRProvability ContextCombination.
Unset Implicit Arguments.
Lemma source_selector_component_bounds M test a b out k:
 source_selector_graph M test a b out->source_bounded M out k->
 source_bounded M test k /\source_bounded M a k /\source_bounded M b k.
Proof.
 intros HG BO. unfold source_selector_graph in HG.
 change(code_relation M(source_reflection_five_env test a b a b)
  (E_sf SFOr(E_sf SFAnd(CEvar 0)(CEvar 1))(E_sf SFAnd(E_sf SFImpl(CEvar 0)(CEconst 0))(CEvar 2)))out)in HG.
 destruct(schema_expression_split M _ SFOr _ _ out HG)as(left&right&HL&HR&HO).
 destruct(schema_expression_split M _ SFAnd _ _ left HL)as(test'&a'&HT&HA&HLAnd).
 change(test'=test)in HT. change(a'=a)in HA. subst test' a'.
 destruct(schema_expression_split M _ SFAnd _ _ right HR)as(negative&b'&HN&HB&HRAnd).
 change(b'=b)in HB. subst b'.
 destruct(proj1(source_bounded_accept_binary M SFOr left right out k(or_intror(or_introl eq_refl))HO)BO)as(BL&BR).
 destruct(proj1(source_bounded_accept_binary M SFAnd test a left k(or_introl eq_refl)HLAnd)BL)as(BT&BA).
 destruct(proj1(source_bounded_accept_binary M SFAnd negative b right k(or_introl eq_refl)HRAnd)BR)as(BN&BB).
 auto.
Qed.
Theorem source_full_native_witness_request M domain theta count beta carrier p s t delta db dc pb pc
 diagonal rawPoint matrix some pp stshift diagonalHole pointHole refl level pY sY tY st gb gc gn k:
 source_bounded M domain(code_numeral M 1)->source_bounded M theta count->context_bounded M gb gc gn k->
 coding_lt M beta k->coding_lt M carrier k->
 source_witness_diagonal_map M p delta db dc->source_witness_point_map M p s t delta pb pc->
 substitution_maps_bound M db dc(code_numeral M 4)delta count k->
 substitution_maps_bound M pb pc(code_numeral M 4)(succM M delta)count(succM M k)->
 numerical_substitution M theta db dc(code_numeral M 4)delta diagonal->
 numerical_substitution M theta pb pc(code_numeral M 4)(succM M delta)rawPoint->
 sf_relation M SFEx matrix(zeroM M)some->sf_relation M SFMember p p pp->
 sf_relation M SFMember(succM M s)(succM M t)stshift->
 source_selector_graph M pp diagonalHole some diagonal->source_selector_graph M stshift matrix pointHole rawPoint->
 source_ordinary_reflection M domain count theta beta refl->source_LL_instance M beta carrier level->
 sf_relation M SFMember p carrier pY->sf_relation M SFMember s carrier sY->sf_relation M SFMember t carrier tY->
 sf_relation M SFMember s t st->source_full_prv M gb gc gn refl->source_full_prv M gb gc gn level->
 source_full_prv M gb gc gn pY->source_full_prv M gb gc gn sY->source_full_prv M gb gc gn tY->source_full_prv M gb gc gn st->
 (forall i name member,coding_lt M i count->substitution_lookup M db dc(code_numeral M 4)delta i name->
  sf_relation M SFMember name carrier member->source_full_prv M gb gc gn member)->
 exists request nb nc nn ub uc un,source_reflected_request_recipe M domain carrier matrix request /\
 source_zfr_context M nb nc nn /\context_union M gb gc gn nb nc nn ub uc un /\source_full_prv M ub uc un request.
Proof.
 intros HD HT BC HB HY HMapD HMapP BMapD BMapP HSubD HSubP HSome HPP HSTShift HSelectorD HSelectorP
  HR HL HPY HSY HTY HST PR PL PPY PSY PTY PST HMembers.
 pose proof(numerical_substitution_preserves_bound M theta db dc(code_numeral M 4)delta diagonal count k HT HSubD BMapD)as BDiagonal.
 pose proof(numerical_substitution_preserves_bound M theta pb pc(code_numeral M 4)(succM M delta)rawPoint count(succM M k)HT HSubP BMapP)as BRawPoint.
 destruct(source_selector_component_bounds M pp diagonalHole some diagonal k HSelectorD BDiagonal)as(BPP&BDiagonalHole&BSome).
 destruct(source_selector_component_bounds M stshift matrix pointHole rawPoint(succM M k)HSelectorP BRawPoint)as(BSTShift&BMatrix&BPointHole).
 destruct(source_relativization_total M domain diagonal)as(classDiagonal&HClassD).
 destruct(source_set_relativization_total M carrier diagonal)as(setDiagonal&HSetD).
 destruct(source_relativization_total M domain rawPoint)as(classPoint&HClassP).
 destruct(source_set_relativization_total M(succM M carrier)rawPoint)as(setPoint&HSetP).
 destruct(source_iff_total M classDiagonal setDiagonal)as(equiv&HEquiv).
 pose proof(source_full_ordinary_reflection_substitution M domain count theta beta refl carrier level db dc(code_numeral M 4)delta
  diagonal classDiagonal setDiagonal equiv gb gc gn k HD HT BC HB HY BMapD HR HL HSubD HClassD HSetD HEquiv PR PL HMembers)as PEquiv.
 destruct(source_iff_parts M classDiagonal setDiagonal equiv HEquiv)as(first&back&HFirst&HBack&HAnd).
 pose proof(source_relativization_preserves_bound M diagonal domain k classDiagonal HD BDiagonal HClassD)as BClassD.
 pose proof(source_set_relativization_preserves_bound M diagonal carrier k setDiagonal HY BDiagonal HSetD)as BSetD.
 pose proof(proj2(source_bounded_accept_binary M SFImpl classDiagonal setDiagonal first k
  (or_intror(or_intror eq_refl))HFirst)(conj BClassD BSetD))as BFirst.
 pose proof(full_source_CE1 M gb gc gn first back equiv(ex_intro _ k(conj BFirst BC))PEquiv HAnd)as PFirst.
 destruct(sf_relation_total M SFMember(zeroM M)(succM M carrier))as(guard&HGuard).
 destruct(sf_relation_total M SFImpl setPoint classPoint)as(reverse&HReverse).
 destruct(sf_relation_total M SFImpl guard reverse)as(point&HPoint).
 destruct(sf_relation_total M SFAll point(zeroM M))as(allpoint&HAll).
 pose proof(source_full_witness_point_reflection M domain theta count beta carrier p s t delta db dc pb pc refl level rawPoint
  classPoint setPoint guard reverse point allpoint pY sY tY gb gc gn k
  HD HT BC HB HY BRawPoint HR HL HMapD HMapP BMapP HSubP HClassP HSetP HGuard HReverse HPoint HAll
  HPY HSY HTY PR PL PPY PSY PTY HMembers)as PAll.
 assert(HShift:source_formula_shift M st stshift).
 { apply(proj2(numerical_renaming_member M s t st(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)stshift HST)).
   exists(succM M s),(succM M t). split;[apply context_shift_lookup;reflexivity|].
   split;[apply context_shift_lookup;reflexivity|exact HSTShift]. }
 exact(source_full_reflected_request_link M gb gc gn k domain carrier p pp s t st stshift diagonalHole matrix pointHole
  some diagonal rawPoint classDiagonal setDiagonal classPoint setPoint first guard reverse point allpoint
  BC HD HY BPP BDiagonalHole BMatrix BPointHole BSTShift HPP HST HShift HSome HSelectorD HSelectorP HClassD HSetD HClassP HSetP
  HFirst HGuard HReverse HPoint HAll PFirst PAll PST).
Qed.
Print Assumptions source_selector_component_bounds.
Print Assumptions source_full_native_witness_request.
