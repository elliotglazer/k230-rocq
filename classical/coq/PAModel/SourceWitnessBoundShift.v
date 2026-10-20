(** The existential witness-bound statement commutes with its outer
    parameter substitution, including an ordinary fresh-variable shift. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
  SourceBoundMonotone SourceOrdinalPredicate NumericalSubstitutionMaps NumericalSubstitution
  SourceSubstitutionIdentity NumericalRenaming RenamingSubstitution SourceQuantifierRules
  SourceFiniteCutoffShift SourceCutoffLiftedSubstitution SourceD0Substitution SourceWitnessBoundGoal.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate source_ordinal_predicate_code.

Theorem source_witness_bound_goal_substitution M domain phi phi' f g k b c n base ab ac an :
  source_bounded M domain(code_numeral M 1) ->source_bounded M phi k ->
  substitution_lift M b c n base ab ac an ->
  numerical_substitution M phi ab ac an(succM M base)phi' ->
  source_witness_bound_goal M domain phi f ->source_witness_bound_goal M domain phi' g ->
  numerical_substitution M f b c n base g.
Proof.
  intros HD HB HL HP(s&d0&body&HC&HD0&HBody&HEx)(s'&d0'&body'&HC'&HD0'&HBody'&HEx').
  destruct(substitution_lift_total M ab ac an(succM M base)) as(tb&tc&tn&HT).
  pose proof(source_cutoff_one_lifted_substitution M phi phi' s s' k b c n base
    ab ac an tb tc tn HB HL HT HP HC HC') as HMatrix.
  assert(HShiftedBound:source_bounded M s(succM M(succM M k))).
  { apply(source_cutoff_shift_bounded M 1 phi s k);[|exact HC].
    exact(source_bounded_monotone M phi k(succM M k)HB
      (coding_lt_trans M k(succM M k)(succM M(succM M k))
        (coding_lt_succ M k)(coding_lt_succ M(succM M k)))). }
  pose proof(source_d0_at_substitution M domain s s'(zeroM M)(zeroM M)d0 d0'
    (succM M(succM M k))ab ac an(succM M base)tb tc tn HD HShiftedBound HT HMatrix
    (proj2(substitution_lift_head M b c n base ab ac an(zeroM M)HL)eq_refl)HD0 HD0') as HD0Sub.
  pose proof(numerical_substitution_lift_fixes_domain M(source_ordinal_predicate_code M)
    b c n base ab ac an(source_ordinal_predicate_bounded M)HL) as HOrd.
  apply(proj2(numerical_substitution_quantifier M false body f b c n base g HEx)).
  exists ab,ac,an,body'. split;[exact HL|]. split;[|exact HEx'].
  apply(proj2(numerical_substitution_binary M SFAnd(source_ordinal_predicate_code M)d0 body
    ab ac an(succM M base)body'(or_introl eq_refl)HBody)).
  exists(source_ordinal_predicate_code M),d0'. repeat split;assumption.
Qed.

Theorem source_witness_bound_goal_shift M domain phi phi' goal shifted k :
  source_bounded M domain(code_numeral M 1) ->source_bounded M phi k ->
  source_cutoff_shift M 1 phi phi' ->source_witness_bound_goal M domain phi goal ->
  source_formula_shift M goal shifted ->source_witness_bound_goal M domain phi' shifted.
Proof.
  intros HD HB HC HG HS.
  destruct(source_witness_bound_goal_total M domain phi') as(next&HN).
  destruct HC as(ab&ac&an&(u&v&m&(EU&EV&EM)&HL)&HP). subst u v m.
  pose proof(source_witness_bound_goal_substitution M domain phi phi' goal next k
    (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)ab ac an HD HB HL HP HG HN) as HSub.
  pose proof(proj2(numerical_renaming_empty_substitution M goal(zeroM M)(zeroM M)
    (code_numeral M 1)next)HSub) as HR.
  pose proof(numerical_renaming_functional M goal(zeroM M)(zeroM M)(zeroM M)
    (code_numeral M 1)next shifted HR HS) as E. now subst next.
Qed.

Print Assumptions source_witness_bound_goal_substitution.
Print Assumptions source_witness_bound_goal_shift.
