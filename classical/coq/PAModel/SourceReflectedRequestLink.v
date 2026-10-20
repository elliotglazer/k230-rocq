(** Link literal class/set reflection of selector formulas to the actual
    witness-request proof. The set-relative child matrix uses succ(carrier),
    and both reflection statements are ordinary proofs in the caller's
    context. This does not assume or prove the mathematical reflection schema. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
  NumericalContexts NumericalSourceFull ContextCombination NumericalRenaming NumericalRenamingMaps
  NumericalContextRenaming SourceQuantifierRules SourcePropositionalTemplates SourceReflectionSelectors
  SourceReflectedExistential SourceReflectedWitnessRequest SourceRelativizedSelectors
  SourceRelativizationRules SourceRelativization SourceRelativizationFunctionality SourceRelativizationBounds
  SourceSetRelativizationRules SourceSetRelativization SourceSetRelativizationFunctionality
  SourceSetRelativizationBounds SourceZFRProvability.
Unset Implicit Arguments.

Definition source_reflected_request_recipe M domain carrier matrix out :=exists left some bounded,
  source_relativization M domain matrix left /\sr_quantifier M false domain left some /\
  ssr_quantifier M false carrier left bounded /\sf_relation M SFImpl some bounded out.

Theorem source_full_reflected_request_link M cb cc cn k domain carrier p pp s t st stshift
    diagonal matrix other rawSome rawDiagonal rawPoint classDiagonal setDiagonal classPoint setPoint
    first guard reflection point allpoint :
  context_bounded M cb cc cn k ->source_bounded M domain (code_numeral M 1) ->
  coding_lt M carrier k ->source_bounded M pp k ->source_bounded M diagonal k ->
  source_bounded M matrix (succM M k) ->source_bounded M other (succM M k) ->
  source_bounded M stshift (succM M k) ->
  sf_relation M SFMember p p pp ->sf_relation M SFMember s t st ->source_formula_shift M st stshift ->
  sf_relation M SFEx matrix (zeroM M) rawSome ->
  source_selector_graph M pp diagonal rawSome rawDiagonal ->
  source_selector_graph M stshift matrix other rawPoint ->
  source_relativization M domain rawDiagonal classDiagonal ->
  source_set_relativization M carrier rawDiagonal setDiagonal ->
  source_relativization M domain rawPoint classPoint ->
  source_set_relativization M (succM M carrier) rawPoint setPoint ->
  sf_relation M SFImpl classDiagonal setDiagonal first ->
  sf_relation M SFMember (zeroM M)(succM M carrier) guard ->
  sf_relation M SFImpl setPoint classPoint reflection ->
  sf_relation M SFImpl guard reflection point ->sf_relation M SFAll point (zeroM M) allpoint ->
  source_full_prv M cb cc cn first ->source_full_prv M cb cc cn allpoint ->source_full_prv M cb cc cn st ->
  exists request nb nc nn ub uc un,
    source_reflected_request_recipe M domain carrier matrix request /\source_zfr_context M nb nc nn /\
    context_union M cb cc cn nb nc nn ub uc un /\source_full_prv M ub uc un request.
Proof.
  intros HC HD HCarrier HPPB HDiagB HMatrix HOther HSTB HPP HST HShift HSome
    HRawDiag HRawPoint HRDiag HSSetDiag HRPoint HSSetPoint HFirst HGuard HR HPoint HAll PFirst PAll PST.
  assert(HPPC:source_relativization M domain pp pp).
  { exact(source_relativization_atom M domain SFMember p p pp (or_introl eq_refl) HPP). }
  assert(HPPS:source_set_relativization M carrier pp pp).
  { exact(source_set_relativization_atom M carrier SFMember p p pp (or_introl eq_refl) HPP). }
  destruct(source_selector_class_components M domain pp diagonal rawSome rawDiagonal classDiagonal
    HPPC HRawDiag HRDiag) as(diagL&someL&HDiagL&HSomeL&HClassDiag).
  destruct(source_selector_set_components M carrier pp diagonal rawSome rawDiagonal setDiagonal
    HPPS HRawDiag HSSetDiag) as(diagY&someY&HDiagY&HSomeY&HSetDiag).
  destruct(source_relativization_quantifier_inv M domain false matrix rawSome someL HSome HSomeL)
    as(left&HLeft&HExL).
  destruct(source_set_relativization_quantifier_inv M carrier false matrix rawSome someY HSome HSomeY)
    as(right&HRight&guardY&bodyLeft&HGuardY&HBodyLeft&HExY).
  pose proof(sf_relation_functional M SFMember (zeroM M)(succM M carrier) guardY guard HGuardY HGuard) as EG.
  subst guardY.
  destruct(proj1(numerical_renaming_member M s t st (zeroM M)(zeroM M)(zeroM M)
    (code_numeral M 1) stshift HST) HShift) as(s'&t'&HS'&HT'&HST').
  apply context_shift_lookup in HS'. apply context_shift_lookup in HT'. subst s' t'.
  assert(HSTC:source_relativization M domain stshift stshift).
  { exact(source_relativization_atom M domain SFMember (succM M s)(succM M t) stshift
      (or_introl eq_refl) HST'). }
  assert(HSTS:source_set_relativization M (succM M carrier) stshift stshift).
  { exact(source_set_relativization_atom M (succM M carrier) SFMember (succM M s)(succM M t) stshift
      (or_introl eq_refl) HST'). }
  destruct(source_selector_class_components M domain stshift matrix other rawPoint classPoint
    HSTC HRawPoint HRPoint) as(left'&otherL&HLeft'&HOtherL&HClassPoint).
  pose proof(source_relativization_functional M matrix domain left' left HLeft' HLeft) as EL. subst left'.
  destruct(source_selector_set_components M (succM M carrier) stshift matrix other rawPoint setPoint
    HSTS HRawPoint HSSetPoint) as(right'&otherY&HRight'&HOtherY&HSetPoint).
  pose proof(source_set_relativization_functional M matrix (succM M carrier) right' right HRight' HRight) as ER.
  subst right'.
  destruct(sf_relation_total M SFAnd guard left) as(bodyRight&HBodyRight).
  destruct(sf_relation_total M SFEx bodyRight (zeroM M)) as(boundedL&HBoundedL).
  destruct(sf_relation_total M SFImpl someL boundedL) as(request&HRequest).
  assert(HDiagBounds:forall i,source_bounded M
      (source_reflection_five_env pp diagL someL diagY someY i) k).
  { intros[|[|[|[|[|i]]]]];cbn[source_reflection_five_env];try exact HPPB.
    - exact(source_relativization_preserves_bound M diagonal domain k diagL HD HDiagB HDiagL).
    - apply(source_relativization_preserves_bound M rawSome domain k someL HD);[|exact HSomeL].
      exact(proj2(source_bounded_accept_unary M SFEx matrix rawSome k (or_intror eq_refl) HSome) HMatrix).
    - exact(source_set_relativization_preserves_bound M diagonal carrier k diagY HCarrier HDiagB HDiagY).
    - apply(source_set_relativization_preserves_bound M rawSome carrier k someY HCarrier);[|exact HSomeY].
      exact(proj2(source_bounded_accept_unary M SFEx matrix rawSome k (or_intror eq_refl) HSome) HMatrix). }
  assert(HGuardB:source_bounded M guard (succM M k)).
  { apply(proj2(source_bounded_accept_atom M SFMember (zeroM M)(succM M carrier) guard
      (succM M k)(or_introl eq_refl) HGuard)).
    split;[apply coding_zero_lt_succ|exact(proj2(coding_lt_succ_cancel M carrier k) HCarrier)]. }
  assert(HPointBounds:forall i,source_bounded M
      (source_reflection_five_env stshift right otherY left otherL i)(succM M k)).
  { intros[|[|[|[|[|i]]]]];cbn[source_reflection_five_env];try exact HSTB.
    - exact(source_set_relativization_preserves_bound M matrix (succM M carrier)(succM M k) right
        (proj2(coding_lt_succ_cancel M carrier k) HCarrier) HMatrix HRight).
    - exact(source_set_relativization_preserves_bound M other (succM M carrier)(succM M k) otherY
        (proj2(coding_lt_succ_cancel M carrier k) HCarrier) HOther HOtherY).
    - exact(source_relativization_preserves_bound M matrix domain (succM M k) left HD HMatrix HLeft).
    - exact(source_relativization_preserves_bound M other domain (succM M k) otherL HD HOther HOtherL). }
  assert(HFirstGraph:code_relation M (source_reflection_five_env pp diagL someL diagY someY)
      (source_prop_expression(SPTImpl source_reflection_pair_left source_reflection_pair_right)) first).
  { exact(source_prop_template_join M (source_reflection_five_env pp diagL someL diagY someY)
      SFImpl source_reflection_pair_left source_reflection_pair_right classDiagonal setDiagonal first
      HClassDiag HSetDiag HFirst). }
  assert(HReflectionGraph:code_relation M (source_reflection_five_env stshift right otherY left otherL)
      (source_prop_expression(SPTImpl source_reflection_pair_left source_reflection_pair_right)) reflection).
  { exact(source_prop_template_join M (source_reflection_five_env stshift right otherY left otherL)
      SFImpl source_reflection_pair_left source_reflection_pair_right setPoint classPoint reflection
      HSetPoint HClassPoint HR). }
  destruct(source_full_reflected_witness_request M cb cc cn k p pp diagL diagY someL first
    st stshift guard right left otherY otherL reflection point allpoint bodyLeft bodyRight someY boundedL request
    HC HPP HDiagBounds HGuardB HPointBounds HFirstGraph HShift HReflectionGraph HPoint HAll HBodyLeft HBodyRight
    HExY HBoundedL HRequest PFirst PAll PST) as(nb&nc&nn&ub&uc&un&HNC&HU&PR).
  exists request,nb,nc,nn,ub,uc,un. split;[|auto].
  exists left,someL,boundedL. split;[exact HLeft|]. split;[exact HExL|]. split;[|exact HRequest].
  exists guard,bodyRight. auto.
Qed.

Print Assumptions source_full_reflected_request_link.
