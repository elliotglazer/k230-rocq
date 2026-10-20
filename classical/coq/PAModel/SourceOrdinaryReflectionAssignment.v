(** Ordinary reflection use with an actual arbitrary internal assignment table.
    The domain-membership premises are literal source deductions for each
    beta-table entry, rather than semantic membership or proof preservation. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension BetaPacking CodeExpressions SetFormulaCodes
  SourceBounded SourceBoundMonotone NumericalContexts NumericalSourceFull SourceQuantifierRules SourceDerivedRules
  SourceSubstitutionBounds NumericalInstantiation NumericalSubstitution NumericalSubstitutionMaps SourceRelativization SourceRelativizationBounds
  SourceRelativizationSubstitution SourceRelativizationFunctionality SourceSetRelativization SourceSetRelativizationBounds
  SourceSetRelativizationSubstitution SourceSetRelativizationFunctionality SourceHierarchySyntax SourceMembershipBlocks
  SourceIffGraphs SourceOrdinaryReflectionSyntax SourceReflCarrierInstance SourceBallSInstanceMaps SourceBallSElimination.
Unset Implicit Arguments.
Theorem source_full_ordinary_reflection_assignment M domain count phi d refl y level b c
    phi' left' right' out gb gc gn k:
  source_bounded M domain(code_numeral M 1)->source_bounded M phi count->
  context_bounded M gb gc gn k->coding_lt M d k->coding_lt M y k->
  substitution_maps_bound M b c count(zeroM M)count k->
  source_ordinary_reflection M domain count phi d refl->source_LL_instance M d y level->
  numerical_substitution M phi b c count(zeroM M)phi'->
  source_relativization M domain phi' left'->source_set_relativization M y phi' right'->source_iff_graph M left' right' out->
  source_full_prv M gb gc gn refl->source_full_prv M gb gc gn level->
  balls_member_inputs M gb gc gn y b c count->
  source_full_prv M gb gc gn out.
Proof.
  intros HD HP HC HDK HY HMap HRefl HLevel HPhi' HLeft' HRight' HOut PRefl PLevel HMembers.
  pose proof(source_ordinary_reflection_bounded M domain count phi d refl k HD HP HDK HRefl)as BRefl.
  destruct HRefl as(left&right&equiv&bounded&oldlevel&point&HLeft&HRight&HEquiv&HBounded&HOldLevel&HPoint&HAll).
  destruct(source_refl_carrier_instance M domain count phi d left right equiv bounded oldlevel point y level
    HD HP HLeft HRight HEquiv HBounded HOldLevel HPoint HLevel)
    as(right1&equiv1&bounded1&point1&HRight1&HEquiv1&HBounded1&HPoint1&HInst).
  pose proof(proj1(source_bounded_accept_unary M SFAll point refl k(or_introl eq_refl)HAll)BRefl)as BPoint.
  pose proof(numerical_instantiation_bounded M point y point1 k BPoint HY HInst)as BPoint1.
  pose proof(full_source_AllE M gb gc gn point refl y point1(ex_intro _ k(conj BPoint1 HC))PRefl HAll HInst)as PPoint1.
  pose proof(source_full_modus_ponens M gb gc gn level bounded1 point1 HPoint1 PPoint1 PLevel)as PBounded1.
  destruct(source_relativization_substitution_exists M phi domain b c count(zeroM M)phi' left HD HPhi' HLeft)
    as(left2&HLeft2&HLSub).
  pose proof(source_relativization_functional M phi' domain left2 left' HLeft2 HLeft')as E. subst left2.
  destruct(source_set_relativization_substitution_exists M phi(addM M count y)y b c count(zeroM M)phi' right1
    (balls_prefix_tail M b c count y)HPhi' HRight1)as(right2&HRight2&HRSub).
  pose proof(source_set_relativization_functional M phi' y right2 right' HRight2 HRight')as E. subst right2.
  pose proof(source_iff_substitution M left right1 equiv1 left' right' out b c count(zeroM M)
    HEquiv1 HOut HLSub HRSub)as HEquivSub.
  pose proof(source_bounded_monotone M phi count(addM M count k)HP(coding_le_add M count k))as BPHI.
  pose proof(source_relativization_preserves_bound M phi domain(addM M count k)left HD BPHI HLeft)as BLeft.
  pose proof(source_set_relativization_preserves_bound M phi(addM M count y)(addM M count k)right1
    (coding_lt_add_left M count y k HY)BPHI HRight1)as BRight1.
  pose proof(source_iff_bounded M left right1 equiv1(addM M count k)BLeft BRight1 HEquiv1)as BEquiv1.
  exact(source_full_ballS_elimination M count y equiv1 bounded1 out b c gb gc gn k
    HC HY BEquiv1 HMap HBounded1 HEquivSub PBounded1 HMembers).
Qed.
Print Assumptions source_full_ordinary_reflection_assignment.

