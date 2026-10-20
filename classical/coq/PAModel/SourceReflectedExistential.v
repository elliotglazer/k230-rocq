(** The witness-preserving half of KUpperReflect.reflected_witness_request.
    Reflection is a literal ordinary source proof of the displayed selector
    implication, quantified over the candidate output. Matrices are arbitrary
    internal formula codes; the existential witness is unchanged. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  NumericalContexts NumericalEnvironments NumericalContextRenaming NumericalRenaming
  SourceQuantifierRules NumericalSourceFull SourceSequents SourceTraceBounds SourceProofRenaming
  SourceContextProofHelpers SourceUniversalPropositional SourceExistentialMap SourceConjunctionRules
  SourceDerivedRules SourcePropositionalTemplates SourceReflectionSelectors SchemaConstructorBounds.
Unset Implicit Arguments.

Definition source_reflection_five_env {A:Type} (test left oldright right newright:A) i :=
  match i with 0=>test |1=>left |2=>oldright |3=>right |4=>newright |S(S(S(S(S _))))=>test end.

Theorem source_full_reflected_existential M cb cc cn k st stshift d left right otherleft otherright
    reflection point allpoint bodyLeft bodyRight exLeft exRight :
  context_bounded M cb cc cn k ->source_bounded M d (succM M k) ->
  (forall i,source_bounded M (source_reflection_five_env stshift left otherleft right otherright i)
      (succM M k)) ->
  source_formula_shift M st stshift ->
  code_relation M (source_reflection_five_env stshift left otherleft right otherright)
    (source_prop_expression (SPTImpl source_reflection_pair_left source_reflection_pair_right)) reflection ->
  sf_relation M SFImpl d reflection point ->sf_relation M SFAll point (zeroM M) allpoint ->
  sf_relation M SFAnd d left bodyLeft ->sf_relation M SFAnd d right bodyRight ->
  sf_relation M SFEx bodyLeft (zeroM M) exLeft ->sf_relation M SFEx bodyRight (zeroM M) exRight ->
  source_full_prv M cb cc cn st ->source_full_prv M cb cc cn allpoint ->
  source_full_prv M cb cc cn exLeft ->source_full_prv M cb cc cn exRight.
Proof.
  intros HC HD HH HS HR HP HA HBL HBR HEL HER PST PAll PEx.
  assert(HLeft:source_bounded M left (succM M k)) by exact(HH 1).
  assert(HRight:source_bounded M right (succM M k)) by exact(HH 3).
  assert(HBodyLeft:source_bounded M bodyLeft (succM M k)).
  { apply(proj2(source_bounded_accept_binary M SFAnd d left bodyLeft (succM M k)
      (or_introl eq_refl) HBL)). split;assumption. }
  assert(HBodyRight:source_bounded M bodyRight (succM M k)).
  { apply(proj2(source_bounded_accept_binary M SFAnd d right bodyRight (succM M k)
      (or_introl eq_refl) HBR)). split;assumption. }
  assert(HExRight:source_bounded M exRight k).
  { exact(proj2(source_bounded_accept_unary M SFEx bodyRight exRight k (or_intror eq_refl) HER) HBodyRight). }
  destruct(context_shift_total M cb cc cn) as(sb&sc&HShift).
  destruct(environment_cons_total M sb sc cn bodyLeft) as(ub&uc&un&HCons).
  assert(HBranch:context_bounded M ub uc un (succM M k)).
  { apply(proj2(context_bounded_cons M sb sc cn bodyLeft ub uc un (succM M k) HCons)).
    split;[exact HBodyLeft|exact(context_shift_preserves_bound M cb cc cn sb sc k HShift HC)]. }
  pose proof(source_full_cons_head M sb sc cn bodyLeft ub uc un (succM M k)
    HCons HBodyLeft HBranch) as PBody.
  pose proof(source_full_conjunction_left M ub uc un d left bodyLeft HBL PBody) as PD.
  pose proof(source_full_conjunction_right M ub uc un d left bodyLeft HBL PBody) as PLeft.
  pose proof(source_full_all_shift M cb cc cn point allpoint sb sc HA PAll HShift) as PPoint.
  pose proof(source_full_cons_weaken M sb sc cn bodyLeft ub uc un (succM M k) point HCons HBranch PPoint)
    as PPoint'.
  pose proof(source_full_modus_ponens M ub uc un d reflection point HP PPoint' PD) as PR.
  pose proof(source_full_prv_renaming M cb cc cn st (zeroM M)(zeroM M)(zeroM M)
    (code_numeral M 1) sb sc stshift PST HShift HS) as PS.
  pose proof(source_full_cons_weaken M sb sc cn bodyLeft ub uc un (succM M k) stshift HCons HBranch PS)
    as PS'.
  destruct(sf_relation_total M SFImpl left right) as(imp&HImp).
  assert(HImpGraph:code_relation M (source_reflection_five_env stshift left otherleft right otherright)
      (source_prop_expression(source_reflection_selected false)) imp).
  { exact(proj2(schema_expression_graph M (source_reflection_five_env stshift left otherleft right otherright)
      SFImpl (CEvar 1)(CEvar 3) left right imp eq_refl eq_refl) HImp). }
  pose proof(source_full_reflection_selector M false
    (source_reflection_five_env stshift left otherleft right otherright) (succM M k)
    ub uc un stshift reflection imp HH HBranch eq_refl HR HImpGraph PS' PR) as PI.
  pose proof(source_full_modus_ponens M ub uc un left right imp HImp PI PLeft) as PRight.
  assert(PBodyRight:source_full_prv M ub uc un bodyRight).
  { apply(full_source_CI M ub uc un d right bodyRight);[exists(succM M k);auto|exact PD|exact PRight|exact HBR]. }
  destruct(numerical_renaming_total M exRight (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1))
    as(shifted&HExShift).
  exact(source_full_exists_map M cb cc cn bodyLeft bodyRight exLeft exRight sb sc ub uc un shifted
    (ex_intro _ k (conj HExRight HC)) HEL HER HShift HCons HExShift PEx PBodyRight).
Qed.

Print Assumptions source_full_reflected_existential.
