(** Both reflection-selector steps of reflected_witness_request. The false
    diagonal is justified by the actual ZFR Foundation/no-self derivation.
    Its finite axiom context is added explicitly to the caller's context.
    Reflection itself remains an ordinary, literal source-proof premise. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  SourceBoundMonotone NumericalContexts NumericalEnvironments NumericalSourceFull
  ContextCombination SourceClosedContextShift SourceProofWeakening SourceTraceBounds
  SourceContextProofHelpers SourceDerivedRules SourcePropositionalTemplates SourceReflectionSelectors
  SchemaConstructorBounds SourceQuantifierRules SourceZFRNoSelf SourceZFRProvability SourceReflectedExistential.
Unset Implicit Arguments.

Theorem source_full_reflected_witness_request M cb cc cn k p pp diagonalLeft diagonalRight someL
    first st stshift d left right otherleft otherright reflection point allpoint
    bodyLeft bodyRight someY boundedL request :
  context_bounded M cb cc cn k ->sf_relation M SFMember p p pp ->
  (forall i,source_bounded M (source_reflection_five_env pp diagonalLeft someL diagonalRight someY i) k) ->
  source_bounded M d (succM M k) ->
  (forall i,source_bounded M (source_reflection_five_env stshift left otherleft right otherright i)
      (succM M k)) ->
  code_relation M (source_reflection_five_env pp diagonalLeft someL diagonalRight someY)
    (source_prop_expression(SPTImpl source_reflection_pair_left source_reflection_pair_right)) first ->
  source_formula_shift M st stshift ->
  code_relation M (source_reflection_five_env stshift left otherleft right otherright)
    (source_prop_expression(SPTImpl source_reflection_pair_left source_reflection_pair_right)) reflection ->
  sf_relation M SFImpl d reflection point ->sf_relation M SFAll point (zeroM M) allpoint ->
  sf_relation M SFAnd d left bodyLeft ->sf_relation M SFAnd d right bodyRight ->
  sf_relation M SFEx bodyLeft (zeroM M) someY ->sf_relation M SFEx bodyRight (zeroM M) boundedL ->
  sf_relation M SFImpl someL boundedL request ->
  source_full_prv M cb cc cn first ->source_full_prv M cb cc cn allpoint ->
  source_full_prv M cb cc cn st ->
  exists nb nc nn ub uc un,
    source_zfr_context M nb nc nn /\context_union M cb cc cn nb nc nn ub uc un /\
    source_full_prv M ub uc un request.
Proof.
  intros HC HPP HDiag HD HH HFirst HS HR HP HA HBL HBR HEY HEL HRequest PFirst PAll PST.
  destruct(sf_relation_total M SFImpl pp (zeroM M)) as(negative&HNegative).
  destruct(source_zfr_no_self M p pp negative HPP HNegative) as(nb&nc&nn&HNoSelf&PNegative).
  destruct(context_union_total M cb cc cn nb nc nn) as(ub&uc&un&HUnion).
  assert(HNew:context_bounded M ub uc un k).
  { apply(source_context_union_bounded M cb cc cn nb nc nn ub uc un k HUnion HC).
    exact(context_bounded_monotone M nb nc nn (zeroM M) k
      (source_zfr_context_closed M nb nc nn HNoSelf)(coding_zero_lt_succ M k)). }
  assert(PN:source_full_prv M ub uc un negative).
  { exact(source_full_prv_weaken_bounded M nb nc nn ub uc un negative k PNegative
      (context_union_right M cb cc cn nb nc nn ub uc un HUnion) HNew). }
  assert(PF:source_full_prv M ub uc un first).
  { exact(source_full_prv_weaken_bounded M cb cc cn ub uc un first k PFirst
      (context_union_left M cb cc cn nb nc nn ub uc un HUnion) HNew). }
  assert(PA:source_full_prv M ub uc un allpoint).
  { exact(source_full_prv_weaken_bounded M cb cc cn ub uc un allpoint k PAll
      (context_union_left M cb cc cn nb nc nn ub uc un HUnion) HNew). }
  assert(PS:source_full_prv M ub uc un st).
  { exact(source_full_prv_weaken_bounded M cb cc cn ub uc un st k PST
      (context_union_left M cb cc cn nb nc nn ub uc un HUnion) HNew). }
  assert(HSomeL:source_bounded M someL k) by exact(HDiag 2).
  assert(HBoundedL:source_bounded M boundedL k).
  { apply(proj2(source_bounded_accept_unary M SFEx bodyRight boundedL k (or_intror eq_refl) HEL)).
    apply(proj2(source_bounded_accept_binary M SFAnd d right bodyRight (succM M k)
      (or_introl eq_refl) HBR)). split;[exact HD|exact(HH 3)]. }
  assert(HGoal:source_bounded M request k).
  { apply(proj2(source_bounded_accept_binary M SFImpl someL boundedL request k
      (or_intror(or_intror eq_refl)) HRequest)). split;assumption. }
  destruct(environment_cons_total M ub uc un someL) as(bb&bc&bn&HCons).
  assert(HBranch:context_bounded M bb bc bn k).
  { apply(proj2(context_bounded_cons M ub uc un someL bb bc bn k HCons)). split;assumption. }
  pose proof(source_full_cons_head M ub uc un someL bb bc bn k HCons HSomeL HBranch) as PL.
  pose proof(source_full_cons_weaken M ub uc un someL bb bc bn k negative HCons HBranch PN) as PN'.
  pose proof(source_full_cons_weaken M ub uc un someL bb bc bn k first HCons HBranch PF) as PF'.
  pose proof(source_full_cons_weaken M ub uc un someL bb bc bn k allpoint HCons HBranch PA) as PA'.
  pose proof(source_full_cons_weaken M ub uc un someL bb bc bn k st HCons HBranch PS) as PS'.
  destruct(sf_relation_total M SFImpl someL someY) as(imp&HImp).
  assert(HNegativeGraph:code_relation M
      (source_reflection_five_env pp diagonalLeft someL diagonalRight someY)
      (source_prop_expression(source_reflection_test true)) negative).
  { exact(proj2(schema_expression_graph M
      (source_reflection_five_env pp diagonalLeft someL diagonalRight someY)
      SFImpl (CEvar 0)(CEconst 0) pp (zeroM M) negative eq_refl eq_refl) HNegative). }
  assert(HImpGraph:code_relation M
      (source_reflection_five_env pp diagonalLeft someL diagonalRight someY)
      (source_prop_expression(source_reflection_selected true)) imp).
  { exact(proj2(schema_expression_graph M
      (source_reflection_five_env pp diagonalLeft someL diagonalRight someY)
      SFImpl (CEvar 2)(CEvar 4) someL someY imp eq_refl eq_refl) HImp). }
  pose proof(source_full_reflection_selector M true
    (source_reflection_five_env pp diagonalLeft someL diagonalRight someY) k
    bb bc bn negative first imp HDiag HBranch HNegativeGraph HFirst HImpGraph PN' PF') as PI.
  pose proof(source_full_modus_ponens M bb bc bn someL someY imp HImp PI PL) as PY.
  pose proof(source_full_reflected_existential M bb bc bn k st stshift d left right otherleft otherright
    reflection point allpoint bodyLeft bodyRight someY boundedL HBranch HD HH HS HR HP HA HBL HBR
    HEY HEL PS' PA' PY) as PBounded.
  exists nb,nc,nn,ub,uc,un. split;[exact HNoSelf|]. split;[exact HUnion|].
  apply(full_source_II M ub uc un someL boundedL request bb bc bn).
  - exists k. split;assumption.
  - exact PBounded.
  - exact HCons.
  - exact HRequest.
Qed.

Print Assumptions source_full_reflected_witness_request.
