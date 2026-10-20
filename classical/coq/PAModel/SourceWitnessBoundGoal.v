(** The literal existential conclusion of the uniform witness bound. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
  SourceBoundMonotone SourceOrdinalPredicate SourceFiniteCutoffShift SourceQfFunctionality SourceD0At.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate source_ordinal_predicate_code.

Definition source_witness_bound_goal M domain phi out :=exists shifted d0 body,
  source_cutoff_shift M 1 phi shifted /\source_d0_at M domain shifted(zeroM M)d0 /\
  sf_relation M SFAnd(source_ordinal_predicate_code M)d0 body /\sf_relation M SFEx body(zeroM M)out.

Theorem source_witness_bound_goal_total M domain phi :exists out,source_witness_bound_goal M domain phi out.
Proof.
  destruct(source_cutoff_shift_total M 1 phi) as(shifted&HC).
  destruct(source_d0_at_total M domain shifted(zeroM M)) as(d0&HD).
  destruct(sf_relation_total M SFAnd(source_ordinal_predicate_code M)d0) as(body&HB).
  destruct(sf_relation_total M SFEx body(zeroM M)) as(out&HO).
  exists out,shifted,d0,body. repeat split;assumption.
Qed.

Theorem source_witness_bound_goal_functional M domain phi f g :
  source_witness_bound_goal M domain phi f ->source_witness_bound_goal M domain phi g ->f=g.
Proof.
  intros(s&d&b&HS&HD&HB&HF)(s'&d'&b'&HS'&HD'&HB'&HG).
  pose proof(source_cutoff_shift_functional M 1 phi s s' HS HS') as E. subst s'.
  pose proof(source_d0_at_functional M domain s(zeroM M)d d' HD HD') as E. subst d'.
  pose proof(sf_relation_functional M SFAnd(source_ordinal_predicate_code M)d b b' HB HB') as E. subst b'.
  exact(sf_relation_functional M SFEx b(zeroM M)f g HF HG).
Qed.

Theorem source_witness_bound_goal_bounded M domain phi out k :
  source_bounded M domain(code_numeral M 1) ->source_bounded M phi(succM M k) ->
  source_witness_bound_goal M domain phi out ->source_bounded M out k.
Proof.
  intros HD HB(s&d&b&HS&HD0&HAnd&HEx).
  pose proof(source_cutoff_shift_bounded M 1 phi s k HB HS) as HShiftedBound.
  pose proof(source_d0_at_bounded M domain s(zeroM M)d(succM M k)HD HShiftedBound
    (coding_zero_lt_succ M k)HD0) as HD0Bound.
  apply(proj2(source_bounded_accept_unary M SFEx b out k(or_intror eq_refl)HEx)).
  apply(proj2(source_bounded_accept_binary M SFAnd(source_ordinal_predicate_code M)d b(succM M k)
    (or_introl eq_refl)HAnd)). split;[|exact HD0Bound].
  exact(source_bounded_monotone M(source_ordinal_predicate_code M)(code_numeral M 1)(succM M k)
    (source_ordinal_predicate_bounded M)
    (proj2(coding_lt_succ_cancel M(zeroM M)(succM M k))(coding_zero_lt_succ M k))).
Qed.

Print Assumptions source_witness_bound_goal_total.
Print Assumptions source_witness_bound_goal_functional.
Print Assumptions source_witness_bound_goal_bounded.
