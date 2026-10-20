(** Actual numerical substitutions of witness requests.  This includes
    the arbitrary-set instance needed by the one-level reflection proof. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation SourceSubstitutionIdentity
  SourceEwMonotone SourceD0Substitution SourceFiniteCutoffShift SourceCutoffSingletonCancellation.
Unset Implicit Arguments.

Theorem source_ew_at_substitution M domain matrix matrix' z z' ew ew' b c n base ab ac an :
  source_bounded M domain(code_numeral M 1) ->
  substitution_lift M b c n base ab ac an ->
  numerical_substitution M matrix ab ac an(succM M base) matrix' ->
  substitution_lookup M b c n base z z' ->
  source_ew_at M domain matrix z ew ->source_ew_at M domain matrix' z' ew' ->
  numerical_substitution M ew b c n base ew'.
Proof.
  intros HD HL HM HZ(atom&left&right&HA&HLeft&HRight&HE)
    (atom'&left'&right'&HA'&HLeft'&HRight'&HE').
  assert(HAtom:numerical_substitution M atom ab ac an(succM M base) atom').
  { apply(proj2(numerical_substitution_member M(zeroM M)(succM M z) atom ab ac an
      (succM M base) atom' HA)). exists(zeroM M),(succM M z'). split.
    - exact(proj2(substitution_lift_head M b c n base ab ac an(zeroM M) HL) eq_refl).
    - split;[exact(proj2(substitution_lift_tail M b c n base ab ac an z z' HL) HZ)|exact HA']. }
  pose proof(numerical_substitution_lift_fixes_domain M domain b c n base ab ac an HD HL) as HGuard.
  pose proof(source_guarded_exists_substitution_graph M domain domain matrix matrix' left left'
    b c n base ab ac an HL HGuard HM HLeft HLeft') as HSLeft.
  pose proof(source_guarded_exists_substitution_graph M atom atom' matrix matrix' right right'
    b c n base ab ac an HL HAtom HM HRight HRight') as HSRight.
  apply(proj2(numerical_substitution_binary M SFImpl left right ew b c n base ew'
    (or_intror(or_intror eq_refl)) HE)). exists left',right'. repeat split;assumption.
Qed.

Theorem source_ew_at_specialization M domain phi matrix ew result t k :
  source_bounded M domain(code_numeral M 1) ->source_bounded M phi k ->
  source_cutoff_shift M 1 phi matrix ->
  source_ew_at M domain matrix(zeroM M) ew ->source_ew_at M domain phi t result ->
  numerical_instantiation M ew t result.
Proof.
  intros HD HB HC HE HR.
  destruct(substitution_singleton_total M t) as(b&c&HH&HT).
  destruct(substitution_lift_total M b c(code_numeral M 1)(zeroM M)) as(ab&ac&an&HL).
  exists b,c. split;[exact HH|].
  exact(source_ew_at_substitution M domain matrix phi(zeroM M)t ew result
    b c(code_numeral M 1)(zeroM M)ab ac an HD HL
    (source_cutoff_one_singleton_lift_cancel M phi matrix k b c ab ac an HB HC HL) HH HE HR).
Qed.

Print Assumptions source_ew_at_substitution.
Print Assumptions source_ew_at_specialization.
