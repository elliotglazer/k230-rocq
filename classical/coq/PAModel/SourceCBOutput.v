(** The OC conclusion for Qf becomes exactly the next canonical bounded
    collection goal when its duplicate container parameter is identified.
    The identification is an actual numerical source instantiation. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
  SourceD0Recipe SourceDn SourceDnStep SourceDnBounds SourceQfRecipe SourceQfFunctionality
  SourceCBGoal SourceCBExchange SourceCBCutoffCancellation SourceOrdinalCoverageSyntax
  NumericalSubstitutionMaps NumericalSubstitution NumericalRenaming NumericalInstantiation
  SourceSubstitutionIdentity SourceOrdinalPredicate SourceFiniteCutoffShift SourceCutoffTwoSwap.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code.

Theorem source_cb_oc_output_instantiation M domain level count phi q output goal n:
  source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->
  source_bounded M phi(addM M count(succM M(succM M n))) ->
  source_qf_recipe M domain level count phi q ->source_oc_output_graph M q(code_numeral M 1)output ->
  source_cb_goal M domain level(source_ordinal_predicate_code M)(succM M count)phi goal ->
  numerical_instantiation M output(zeroM M)goal.
Proof.
  intros HD HL HB(d0&previous&HD0&HDN&HQ)(cover&body&HCover&HBody&HEx)
    (d0'&next&body'&HD0'&HDNext&HBody'&HEx').
  pose proof(source_d0_recipe_functional M domain level phi d0' d0 HD0' HD0) as E. subst d0'.
  destruct(proj1(source_dn_succ M count d0 next)HDNext) as(prev'&HDPrev'&HSuccessor).
  pose proof(source_dn_functional M count d0 prev' previous HDPrev' HDN) as E. subst prev'.
  destruct HSuccessor as(rotated&atom&point'&HR&HAtom&HPoint'&HAll').
  destruct HCover as(qV&result&input&point&HC&HS&HInput&HPoint&HAll).
  assert(HB':source_bounded M phi(succM M(addM M count(succM M n)))).
  { rewrite <-qf_add_succ_right. exact HB. }
  pose proof(source_d0_recipe_bounded M domain level phi d0(addM M count(succM M n))HD HL HB' HD0) as HD0B.
  rewrite <-qf_add_succ_right,<-qf_add_succ_right in HD0B.
  pose proof(source_dn_bounded M count d0 previous(succM M n)HDN HD0B) as HPreviousB.
  pose proof(source_dn_rotate_bounded M previous rotated n HPreviousB HR) as HRotatedB.
  assert(HQRecipe:source_qf_recipe M domain level count phi q) by(exists d0,previous;auto).
  pose proof(source_qf_recipe_bounded M domain level count phi q n HD HL HB HQRecipe) as HQB.
  pose proof(source_qf_exchange_swap_rotate M previous q rotated(succM M(succM M(succM M n)))
    HPreviousB HQ HR) as HQSwap.
  destruct(source_cutoff_shift_total M 2 rotated) as(result'&HCResult).
  pose proof(source_cutoff_two_swap M q qV rotated result'(succM M(succM M(succM M n)))
    HQB HC HQSwap HCResult) as HS'.
  pose proof(numerical_renaming_functional M qV(code_numeral M 3)(code_numeral M 1)(code_numeral M 2)
    (zeroM M)result' result HS' HS) as E. subst result'.
  destruct(substitution_singleton_total M(zeroM M)) as(b&c&HHead&HTail).
  destruct(substitution_lift_total M b c(code_numeral M 1)(zeroM M)) as(ab&ac&an&HL1).
  destruct(substitution_lift_total M ab ac an(code_numeral M 1)) as(tb&tc&tn&HL2).
  pose proof(source_cutoff_two_singleton_double_lift_cancel M rotated result
    (succM M(succM M(succM M n)))b c ab ac an tb tc tn HRotatedB HCResult HL1 HL2) as HResultSub.
  assert(HInputSub:numerical_substitution M input tb tc tn(code_numeral M 2)atom).
  { apply(proj2(numerical_substitution_member M(zeroM M)(code_numeral M 2)input tb tc tn(code_numeral M 2)atom HInput)).
    exists(zeroM M),(code_numeral M 2). split.
    - exact(proj2(substitution_lift_head M ab ac an(code_numeral M 1)tb tc tn(zeroM M)HL2)eq_refl).
    - split;[|exact HAtom].
      apply(proj2(substitution_lift_tail M ab ac an(code_numeral M 1)tb tc tn(code_numeral M 1)(code_numeral M 1)HL2)).
      apply(proj2(substitution_lift_tail M b c(code_numeral M 1)(zeroM M)ab ac an(zeroM M)(zeroM M)HL1)).
      exact HHead. }
  assert(HCoverSub:numerical_substitution M cover ab ac an(code_numeral M 1)next).
  { apply(proj2(numerical_substitution_quantifier M true point cover ab ac an(code_numeral M 1)next HAll)).
    exists tb,tc,tn,point'. split;[exact HL2|]. split;[|exact HAll'].
    apply(proj2(numerical_substitution_binary M SFImpl input result point tb tc tn(code_numeral M 2)point'
      (or_intror(or_intror eq_refl))HPoint)). exists atom,rotated. repeat split;assumption. }
  pose proof(numerical_substitution_lift_fixes_domain M(source_ordinal_predicate_code M)b c(code_numeral M 1)
    (zeroM M)ab ac an(source_ordinal_predicate_bounded M)HL1) as HOrdinalSub.
  exists b,c. split;[exact HHead|].
  apply(proj2(numerical_substitution_quantifier M false body output b c(code_numeral M 1)(zeroM M)goal HEx)).
  exists ab,ac,an,body'. split;[exact HL1|]. split;[|exact HEx'].
  apply(proj2(numerical_substitution_binary M SFAnd(source_ordinal_predicate_code M)cover body ab ac an
    (code_numeral M 1)body'(or_introl eq_refl)HBody)).
  exists(source_ordinal_predicate_code M),next. repeat split;assumption.
Qed.

Print Assumptions source_cb_oc_output_instantiation.
