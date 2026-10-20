(** Genuine guarded output-universal reflection from one ordinary Refl
 proof. The four point names and entire parameter tail have actual source
 membership proofs, with the bound output supplied by the guard. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 SourceRelativization SourceRelativizationBounds SourceSetRelativization SourceSetRelativizationBounds
 SourceOrdinaryReflectionSyntax SourceOrdinaryReflectionSubstitution SourceNativeReflectionShift SourceHierarchySyntax
 SourceWitnessThetaInstances SourceWitnessPointMembers SourceSubstitutionBounds NumericalSubstitutionMaps NumericalSubstitution
 SourceIffGraphs NumericalContexts NumericalEnvironments NumericalContextRenaming NumericalSourceFull
 SourceQuantifierRules SourceContextProofHelpers SourceDerivedRules.
Unset Implicit Arguments.
Theorem source_full_witness_point_reflection M domain theta count beta carrier p s t delta db dc pb pc
 refl level rawPoint classPoint setPoint guard reverse point allpoint pY sY tY gb gc gn k:
 source_bounded M domain(code_numeral M 1)->source_bounded M theta count->context_bounded M gb gc gn k->
 coding_lt M beta k->coding_lt M carrier k->source_bounded M rawPoint(succM M k)->
 source_ordinary_reflection M domain count theta beta refl->source_LL_instance M beta carrier level->
 source_witness_diagonal_map M p delta db dc->source_witness_point_map M p s t delta pb pc->
 substitution_maps_bound M pb pc(code_numeral M 4)(succM M delta)count(succM M k)->
 numerical_substitution M theta pb pc(code_numeral M 4)(succM M delta)rawPoint->
 source_relativization M domain rawPoint classPoint->source_set_relativization M(succM M carrier)rawPoint setPoint->
 sf_relation M SFMember(zeroM M)(succM M carrier)guard->sf_relation M SFImpl setPoint classPoint reverse->
 sf_relation M SFImpl guard reverse point->sf_relation M SFAll point(zeroM M)allpoint->
 sf_relation M SFMember p carrier pY->sf_relation M SFMember s carrier sY->sf_relation M SFMember t carrier tY->
 source_full_prv M gb gc gn refl->source_full_prv M gb gc gn level->
 source_full_prv M gb gc gn pY->source_full_prv M gb gc gn sY->source_full_prv M gb gc gn tY->
 (forall i name member,coding_lt M i count->substitution_lookup M db dc(code_numeral M 4)delta i name->
  sf_relation M SFMember name carrier member->source_full_prv M gb gc gn member)->
 source_full_prv M gb gc gn allpoint.
Proof.
 intros HD HT BC HB HY BR HR HL HMapD HMapP HBMap HSub HClass HSet HGuard HReverse HPoint HAll
  HPY HSY HTY PR PL PPY PSY PTY HMembers.
 pose proof(source_relativization_preserves_bound M rawPoint domain(succM M k)classPoint HD BR HClass)as BClass.
 pose proof(source_set_relativization_preserves_bound M rawPoint(succM M carrier)(succM M k)setPoint
  (proj2(coding_lt_succ_cancel M carrier k)HY)BR HSet)as BSet.
 pose proof(proj2(source_bounded_accept_binary M SFImpl setPoint classPoint reverse(succM M k)
  (or_intror(or_intror eq_refl))HReverse)(conj BSet BClass))as BReverse.
 assert(BGuard:source_bounded M guard(succM M k)).
 { apply(proj2(source_bounded_accept_atom M SFMember(zeroM M)(succM M carrier)guard(succM M k)
   (or_introl eq_refl)HGuard)). split;[apply coding_zero_lt_succ|exact(proj2(coding_lt_succ_cancel M carrier k)HY)]. }
 pose proof(proj2(source_bounded_accept_binary M SFImpl guard reverse point(succM M k)
  (or_intror(or_intror eq_refl))HPoint)(conj BGuard BReverse))as BPoint.
 pose proof(proj2(source_bounded_accept_unary M SFAll point allpoint k(or_introl eq_refl)HAll)BPoint)as BAll.
 destruct(context_shift_total M gb gc gn)as(sb&sc&HShift).
 pose proof(context_shift_preserves_bound M gb gc gn sb sc k HShift BC)as BS.
 destruct(source_full_ordinary_reflection_shift M domain count theta beta carrier refl level gb gc gn sb sc
  HD HT HR HL HShift PR PL)as(reflS&levelS&HRefS&HLevelS&PRefS&PLevelS).
 destruct(environment_cons_total M sb sc gn guard)as(ub&uc&un&HCons).
 pose proof(proj2(context_bounded_cons M sb sc gn guard ub uc un(succM M k)HCons)(conj BGuard BS))as BU.
 pose proof(source_full_cons_weaken M sb sc gn guard ub uc un(succM M k)reflS HCons BU PRefS)as PRef.
 pose proof(source_full_cons_weaken M sb sc gn guard ub uc un(succM M k)levelS HCons BU PLevelS)as PLevel.
 destruct(source_iff_total M classPoint setPoint)as(equiv&HEquiv).
 assert(PMembers:forall i name member,coding_lt M i count->
  substitution_lookup M pb pc(code_numeral M 4)(succM M delta)i name->
  sf_relation M SFMember name(succM M carrier)member->source_full_prv M ub uc un member).
 { intros i name member HI HName HMember.
   destruct(source_witness_point_lookup_cases M p s t delta db dc pb pc i name HMapD HMapP HName)
    as[E|[E|[E|[E|(old&HOld&E)]]]];subst name.
   - pose proof(sf_relation_functional M SFMember(zeroM M)(succM M carrier)member guard HMember HGuard)as E;subst member.
     exact(source_full_cons_head M sb sc gn guard ub uc un(succM M k)HCons BGuard BU).
   - exact(source_full_cons_weaken M sb sc gn guard ub uc un(succM M k)member HCons BU
      (source_full_shifted_member M gb gc gn sb sc p carrier pY member HShift HPY HMember PPY)).
   - exact(source_full_cons_weaken M sb sc gn guard ub uc un(succM M k)member HCons BU
      (source_full_shifted_member M gb gc gn sb sc s carrier sY member HShift HSY HMember PSY)).
   - exact(source_full_cons_weaken M sb sc gn guard ub uc un(succM M k)member HCons BU
      (source_full_shifted_member M gb gc gn sb sc t carrier tY member HShift HTY HMember PTY)).
   - destruct(sf_relation_total M SFMember old carrier)as(oldMember&HOldMember).
     pose proof(HMembers i old oldMember HI HOld HOldMember)as POld.
     exact(source_full_cons_weaken M sb sc gn guard ub uc un(succM M k)member HCons BU
      (source_full_shifted_member M gb gc gn sb sc old carrier oldMember member HShift HOldMember HMember POld)). }
 pose proof(source_full_ordinary_reflection_substitution M domain count theta(succM M beta)reflS(succM M carrier)levelS
  pb pc(code_numeral M 4)(succM M delta)rawPoint classPoint setPoint equiv ub uc un(succM M k)
  HD HT BU(proj2(coding_lt_succ_cancel M beta k)HB)(proj2(coding_lt_succ_cancel M carrier k)HY)
  HBMap HRefS HLevelS HSub HClass HSet HEquiv PRef PLevel PMembers)as PEquiv.
 destruct(source_iff_parts M classPoint setPoint equiv HEquiv)as(forward&back&HForward&HBack&HAnd).
 pose proof(sf_relation_functional M SFImpl setPoint classPoint back reverse HBack HReverse)as E;subst back.
 pose proof(full_source_CE2 M ub uc un forward reverse equiv(ex_intro _ (succM M k)(conj BReverse BU))PEquiv HAnd)as PReverse.
 apply(full_source_AllI M gb gc gn point allpoint sb sc(ex_intro _ k(conj BAll BC)));[|exact HShift|exact HAll].
 exact(full_source_II M sb sc gn guard reverse point ub uc un(ex_intro _ (succM M k)(conj BPoint BS))PReverse HCons HPoint).
Qed.
Print Assumptions source_full_witness_point_reflection.
