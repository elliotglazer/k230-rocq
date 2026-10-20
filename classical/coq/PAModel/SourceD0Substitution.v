(** The one-level witness condition commutes with actual source
    substitutions. Its varying matrix is transported under its witness
    binder, and the hierarchy-set binder is inserted internally. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  NumericalSubstitutionMaps NumericalSubstitution SourceSubstitutionIdentity
  SourceRelativizationRules SourceFiniteCutoffShift SourceHierarchySyntax SourceD0At SourceD0Recipe
  SourceCutoffLiftedSubstitution.
Unset Implicit Arguments.

Theorem source_guarded_exists_substitution_graph M guard guard' matrix matrix' ex ex'
    b c n base ub uc un :
  substitution_lift M b c n base ub uc un ->
  numerical_substitution M guard ub uc un(succM M base) guard' ->
  numerical_substitution M matrix ub uc un(succM M base) matrix' ->
  sr_quantifier M false guard matrix ex ->sr_quantifier M false guard' matrix' ex' ->
  numerical_substitution M ex b c n base ex'.
Proof.
  intros HL HG HM(body&HB&HE)(body'&HB'&HE').
  apply(proj2(numerical_substitution_quantifier M false body ex b c n base ex' HE)).
  exists ub,uc,un,body'. split;[exact HL|]. split;[|exact HE'].
  apply(proj2(numerical_substitution_binary M SFAnd guard matrix body ub uc un(succM M base)
    body'(or_introl eq_refl) HB)). exists guard',matrix'. repeat split;assumption.
Qed.

Theorem source_d0_at_substitution M domain phi phi' d d' out out' k b c n base ab ac an :
  source_bounded M domain(code_numeral M 1) ->source_bounded M phi k ->
  substitution_lift M b c n base ab ac an ->
  numerical_substitution M phi ab ac an(succM M base) phi' ->
  substitution_lookup M b c n base d d' ->
  source_d0_at M domain phi d out ->source_d0_at M domain phi' d' out' ->
  numerical_substitution M out b c n base out'.
Proof.
  intros HD HB HL HP HDN(s&level&ew&point&HC&HLevel&HEw&HPoint&HAll)
    (s'&level'&ew'&point'&HC'&HLevel'&HEw'&HPoint'&HAll').
  destruct(substitution_lift_total M ab ac an(succM M base)) as (tb&tc&tn&HT).
  pose proof(source_cutoff_one_lifted_substitution M phi phi' s s' k
    b c n base ab ac an tb tc tn HB HL HT HP HC HC') as HMatrix.
  pose proof(source_LL_instance_substitution M(succM M d)(zeroM M) level
    (succM M d')(zeroM M) level' ab ac an(succM M base) HLevel HLevel'
    (proj2(substitution_lift_tail M b c n base ab ac an d d' HL) HDN)
    (proj2(substitution_lift_head M b c n base ab ac an(zeroM M) HL) eq_refl)) as HLev.
  change(source_ew_recipe M domain s ew) in HEw.
  change(source_ew_recipe M domain s' ew') in HEw'.
  destruct HEw as(atom&left&right&HA&HLeft&HRight&HE).
  destruct HEw' as(atom'&left'&right'&HA'&HLeft'&HRight'&HE').
  assert(HAtom:numerical_substitution M atom tb tc tn(succM M(succM M base)) atom').
  { apply(proj2(numerical_substitution_member M(zeroM M)(code_numeral M 1) atom
      tb tc tn(succM M(succM M base)) atom' HA)).
    exists(zeroM M),(code_numeral M 1). split.
    - exact(proj2(substitution_lift_head M ab ac an(succM M base) tb tc tn(zeroM M) HT) eq_refl).
    - split;[|exact HA'].
      exact(proj2(substitution_lift_tail M ab ac an(succM M base) tb tc tn(zeroM M)(zeroM M) HT)
        (proj2(substitution_lift_head M b c n base ab ac an(zeroM M) HL) eq_refl)). }
  pose proof(numerical_substitution_lift_fixes_domain M domain ab ac an(succM M base)
    tb tc tn HD HT) as HGuard.
  pose proof(source_guarded_exists_substitution_graph M domain domain s s' left left'
    ab ac an(succM M base) tb tc tn HT HGuard HMatrix HLeft HLeft') as HLeftSub.
  pose proof(source_guarded_exists_substitution_graph M atom atom' s s' right right'
    ab ac an(succM M base) tb tc tn HT HAtom HMatrix HRight HRight') as HRightSub.
  assert(HEwSub:numerical_substitution M ew ab ac an(succM M base) ew').
  { apply(proj2(numerical_substitution_binary M SFImpl left right ew ab ac an(succM M base)
      ew'(or_intror(or_intror eq_refl)) HE)). exists left',right'. repeat split;assumption. }
  apply(proj2(numerical_substitution_quantifier M true point out b c n base out' HAll)).
  exists ab,ac,an,point'. split;[exact HL|]. split;[|exact HAll'].
  apply(proj2(numerical_substitution_binary M SFImpl level ew point ab ac an(succM M base)
    point'(or_intror(or_intror eq_refl)) HPoint)). exists level',ew'. repeat split;assumption.
Qed.

Print Assumptions source_guarded_exists_substitution_graph.
Print Assumptions source_d0_at_substitution.
