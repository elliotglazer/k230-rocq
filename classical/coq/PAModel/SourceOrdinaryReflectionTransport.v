(** Actual arbitrary-map substitution of the ordinal name in ordinary Refl.
    Its internally many bounded parameters are captured, leaving only the
    ordinal name free. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes
 SourceBounded SourceBoundMonotone SourceRelativization SourceRelativizationFunctionality SourceRelativizationBounds
 SourceSetRelativization SourceSetRelativizationFunctionality SourceSetRelativizationBounds
 SourceIffGraphs SourceBallS SourceBallSBounds SourceInternalLiftLaws SourceOrdinaryReflectionSyntax
 SourceHierarchySyntax NumericalSubstitutionMaps NumericalSubstitution SourceSubstitutionIdentity.
Unset Implicit Arguments.
Theorem source_reflection_block_bounded M domain count phi a b equiv block:
 source_bounded M domain(code_numeral M 1)->source_bounded M phi count->
 source_relativization M domain phi a->source_set_relativization M count phi b->
 source_iff_graph M a b equiv->source_ballS M count(zeroM M)equiv block->
 source_bounded M block(code_numeral M 1).
Proof.
 intros HD HP HA HB HE HBL.
 pose proof(source_relativization_preserves_bound M phi domain count a HD HP HA)as BA.
 assert(BPhi1:source_bounded M phi(succM M count)).
 { exact(source_bounded_monotone M phi count(succM M count)HP
    (proj2(coding_lt_succ_cases M count(succM M count))(or_introl(coding_lt_succ M count)))). }
 pose proof(source_set_relativization_preserves_bound M phi count(succM M count)b(coding_lt_succ M count)BPhi1 HB)as BB.
 assert(BA1:source_bounded M a(succM M count)).
 { exact(source_bounded_monotone M a count(succM M count)BA
    (proj2(coding_lt_succ_cases M count(succM M count))(or_introl(coding_lt_succ M count)))). }
 pose proof(source_iff_bounded M a b equiv(succM M count)BA1 BB HE)as BE.
 assert(BE':source_bounded M equiv(addM M count(code_numeral M 1))).
 { change(source_bounded M equiv(addM M count(succM M(zeroM M)))). now rewrite internal_add_succ_right,coding_add_zero_r. }
 exact(source_ballS_bounded M count(zeroM M)equiv block(code_numeral M 1)HBL(coding_zero_lt_succ M(zeroM M))BE').
Qed.
Theorem source_ordinary_reflection_substitution M domain count phi d old d' new b c n base:
 source_bounded M domain(code_numeral M 1)->source_bounded M phi count->
 source_ordinary_reflection M domain count phi d old->source_ordinary_reflection M domain count phi d' new->
 substitution_lookup M b c n base d d'->numerical_substitution M old b c n base new.
Proof.
 intros HD HP(a&z&e&block&level&point&HA&HZ&HE&HB&HL&HPoint&HOld)
  (a'&z'&e'&block'&level'&point'&HA'&HZ'&HE'&HB'&HL'&HPoint'&HNew)HName.
 pose proof(source_relativization_functional M phi domain a a' HA HA')as E;subst a'.
 pose proof(source_set_relativization_functional M phi count z z' HZ HZ')as E;subst z'.
 pose proof(source_iff_functional M a z e e' HE HE')as E;subst e'.
 pose proof(source_ballS_functional M count(zeroM M)e block block' HB HB')as E;subst block'.
 pose proof(source_reflection_block_bounded M domain count phi a z e block HD HP HA HZ HE HB)as BBlock.
 destruct(substitution_lift_total M b c n base)as(rb&rc&rn&HM).
 apply(proj2(numerical_substitution_quantifier M true point old b c n base new HOld)).
 exists rb,rc,rn,point'. split;[exact HM|]. split;[|exact HNew].
 apply(proj2(numerical_substitution_binary M SFImpl level block point rb rc rn(succM M base)point'
  (or_intror(or_intror eq_refl))HPoint)). exists level',block. split.
 - exact(source_LL_instance_substitution M(succM M d)(zeroM M)level(succM M d')(zeroM M)level'
    rb rc rn(succM M base)HL HL'(proj2(proj2 HM)d d' HName)(proj1(proj2 HM))).
 - split;[exact(numerical_substitution_lift_fixes_domain M block b c n base rb rc rn BBlock HM)|exact HPoint'].
Qed.
Print Assumptions source_reflection_block_bounded.
Print Assumptions source_ordinary_reflection_substitution.
