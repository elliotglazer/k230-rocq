(** An actual ZFR proof map for different assignment guards. The guard
    implication is an ordinary source proof, not an equality inference rule. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  SourceBoundMonotone SourceImplicationAllShift SourceQuantifierRules SourcePropositionalTemplates SourceFunctionalityShells
  SourceCarrierGuardProgram SourceDescriptorConditionalPlain SourceDescriptorProvability SourceSetTheoryDescriptors
  SourceZFRProvability SourceWitnessProofComposition.
Unset Implicit Arguments.
Definition source_carrier_guard_environment {A}(condition a b oldguard newguard:A)i:=
  match i with 0=>condition|1=>a|2=>b|3=>oldguard|4=>newguard|_=>condition end.

Theorem source_zfr_conditional_two_guard_universal M condition shifted a b oldguard newguard ab payload gm guardlaw
    oldpoint newpoint pointmap point qa qb qmap result k :
  source_bounded M condition k ->source_formula_shift M condition shifted ->
  source_bounded M a(succM M k) ->source_bounded M b(succM M k) ->
  source_bounded M oldguard(succM M k) ->source_bounded M newguard(succM M k) ->
  sf_relation M SFImpl a b ab ->sf_relation M SFImpl shifted ab payload ->
  sf_relation M SFImpl newguard oldguard gm ->sf_relation M SFImpl shifted gm guardlaw ->
  sf_relation M SFImpl oldguard a oldpoint ->sf_relation M SFImpl newguard b newpoint ->
  sf_relation M SFImpl oldpoint newpoint pointmap ->sf_relation M SFImpl shifted pointmap point ->
  sf_relation M SFAll oldpoint(zeroM M)qa ->sf_relation M SFAll newpoint(zeroM M)qb ->
  sf_relation M SFImpl qa qb qmap ->sf_relation M SFImpl condition qmap result ->
  source_zfr_provable M payload ->source_zfr_provable M guardlaw ->source_zfr_provable M result.
Proof.
  intros HC HS HA HB HG HN HAB HP HGM HGuard HO HNew HMap HPoint HQA HQB HQMap HResult PP PG.
  pose proof(source_shift_bound M condition shifted k HC HS)as HShifted.
  set(rho:=source_carrier_guard_environment shifted a b oldguard newguard).
  assert(HRho:forall i,source_bounded M(rho i)(succM M k)).
  { intros[|[|[|[|[|i]]]]];unfold rho,source_carrier_guard_environment;assumption. }
  assert(HPGraph:code_relation M rho(source_prop_expression carrier_body_map)payload).
  { unfold rho,source_carrier_guard_environment,source_prop_expression,carrier_body_map. functionality_graph. }
  assert(HGGraph:code_relation M rho(source_prop_expression carrier_guard_map)guardlaw).
  { unfold rho,source_carrier_guard_environment,source_prop_expression,carrier_guard_map. functionality_graph. }
  assert(HPointGraph:code_relation M rho(source_prop_expression carrier_point_map)point).
  { unfold rho,source_carrier_guard_environment,source_prop_expression,carrier_point_map. functionality_graph. }
  pose proof(source_zfr_prop_two M carrier_body_map carrier_guard_map carrier_point_map source_carrier_guard_program
    rho(succM M k)payload guardlaw point HRho HPGraph HGGraph HPointGraph PP PG)as PPoint.
  assert(HBOld:source_bounded M oldpoint(succM M k)).
  { exact(proj2(source_bounded_accept_binary M SFImpl oldguard a oldpoint _
      (or_intror(or_intror eq_refl))HO)(conj HG HA)). }
  assert(HBNew:source_bounded M newpoint(succM M k)).
  { exact(proj2(source_bounded_accept_binary M SFImpl newguard b newpoint _
      (or_intror(or_intror eq_refl))HNew)(conj HN HB)). }
  apply(proj1(source_zfr_descriptor_provable M result)).
  exact(source_descriptor_conditional_universal_plain M ZFRSourceDescriptor condition shifted oldpoint newpoint pointmap point
    qa qb qmap result k HC HS HBOld HBNew HMap HPoint HQA HQB HQMap HResult
    (proj2(source_zfr_descriptor_provable M point)PPoint)).
Qed.
Print Assumptions source_zfr_conditional_two_guard_universal.
