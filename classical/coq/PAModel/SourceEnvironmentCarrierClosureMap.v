(** Actual source-proof transfer of closure-container existence along a
    proved implication between arbitrary internally coded carriers. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SetSchemaConstructors
  SourceBounded SourceBoundMonotone SourceBoundedCalibration SourceNumeralLift
  SourceEnvironmentCarrierClosure SourceRepresentationClosureRecipe SourceRepresentationFalsityClosure
  SourceDefinabilityPrimitives SourceDescriptorProvability SourceDescriptorClosure SourceDescriptorPrograms
  SourceDescriptorExistentialMap SourcePropositionalTemplates SchemaConstructorBounds
  SourceZFRProvability SourceSetTheoryDescriptors.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Theorem source_descriptor_carrier_pair_map M T repA repB bodyA bodyB point bodypoint :
  source_bounded M repA(code_numeral M 2) ->source_bounded M repB(code_numeral M 2) ->
  sf_relation M SFAnd(representation_member_code M)repA bodyA ->
  sf_relation M SFAnd(representation_member_code M)repB bodyB ->
  sf_relation M SFImpl repA repB point ->sf_relation M SFImpl bodyA bodyB bodypoint ->
  source_descriptor_provable M T point ->source_descriptor_provable M T bodypoint.
Proof.
  intros BA BB HA HB HP HBP PP.
  set(rho:=schema_env3 repA repB(representation_member_code M)).
  assert(BA4:source_bounded M repA(code_numeral M 4)).
  { apply(source_bounded_monotone M repA(code_numeral M 2)(code_numeral M 4)BA).
    do 2 apply coding_lt_succ_cancel. apply coding_zero_lt_succ. }
  assert(BB4:source_bounded M repB(code_numeral M 4)).
  { apply(source_bounded_monotone M repB(code_numeral M 2)(code_numeral M 4)BB).
    do 2 apply coding_lt_succ_cancel. apply coding_zero_lt_succ. }
  assert(BM:source_bounded M(representation_member_code M)(code_numeral M 4)).
  { apply(proj2(source_bounded_accept_atom M SFMember(zeroM M)(code_numeral M 3)
      (representation_member_code M)(code_numeral M 4)(or_introl eq_refl)(sf_make_numeral M SFMember 0 3))).
    split;[apply coding_zero_lt_succ|apply coding_lt_succ]. }
  assert(P:source_prop_program[SPTImpl(SPTSlot 0)(SPTSlot 1)]
    (SPTImpl(SPTAnd(SPTSlot 2)(SPTSlot 0))(SPTAnd(SPTSlot 2)(SPTSlot 1)))).
  { apply SPTII,SPTCI.
    - apply SPTCE1 with(b:=SPTSlot 0). apply SPTCtx. cbn;auto.
    - eapply SPTIE;[apply SPTCtx;cbn;auto|].
      apply SPTCE2 with(a:=SPTSlot 2). apply SPTCtx. cbn;auto. }
  apply(source_descriptor_prop_program M T _ _ P rho(code_numeral M 4)bodypoint).
  - intros[|[|i]];cbn[rho schema_env3];assumption.
  - intros p[<-|[]]f HF.
    assert(GP:code_relation M rho(source_prop_expression(SPTImpl(SPTSlot 0)(SPTSlot 1)))point).
    { exact(proj2(schema_expression_graph M rho SFImpl(CEvar 0)(CEvar 1)_ _ point eq_refl eq_refl)HP). }
    rewrite(code_relation_functional M _ rho f point HF GP). exact PP.
  - assert(GA:code_relation M rho(source_prop_expression(SPTAnd(SPTSlot 2)(SPTSlot 0)))bodyA).
    { exact(proj2(schema_expression_graph M rho SFAnd(CEvar 2)(CEvar 0)_ _ bodyA eq_refl eq_refl)HA). }
    assert(GB:code_relation M rho(source_prop_expression(SPTAnd(SPTSlot 2)(SPTSlot 1)))bodyB).
    { exact(proj2(schema_expression_graph M rho SFAnd(CEvar 2)(CEvar 1)_ _ bodyB eq_refl eq_refl)HB). }
    exact(proj2(schema_expression_graph M rho SFImpl _ _ bodyA bodyB bodypoint GA GB)HBP).
Qed.

Theorem source_zfr_environment_carrier_closure_map M repA repB outA outB point :
  source_bounded M repA(code_numeral M 2) ->source_bounded M repB(code_numeral M 2) ->
  source_environment_carrier_closure_statement M repA outA ->
  source_environment_carrier_closure_statement M repB outB ->
  sf_relation M SFImpl repA repB point ->source_descriptor_provable M ZFRSourceDescriptor point ->
  source_zfr_provable M outA ->source_zfr_provable M outB.
Proof.
  intros BA BB HOutA HOutB HPoint PPoint POutA.
  set(succ:=code_numeral M(sf_encode source_def_successor01)).
  set(closure:=code_numeral M(sf_encode representation_closure_condition)).
  destruct(sf_relation_total M SFAnd(representation_member_code M)repA)as(bodyA&HBA).
  destruct(sf_relation_total M SFAnd(representation_member_code M)repB)as(bodyB&HBB).
  destruct(sf_relation_total M SFEx bodyA(zeroM M))as(exA&HEA).
  destruct(sf_relation_total M SFEx bodyB(zeroM M))as(exB&HEB).
  destruct(sf_relation_total M SFImpl closure exA)as(midA&HMA).
  destruct(sf_relation_total M SFImpl closure exB)as(midB&HMB).
  destruct(sf_relation_total M SFImpl succ midA)as(resultA&HRA).
  destruct(sf_relation_total M SFImpl succ midB)as(resultB&HRB).
  pose proof(source_environment_carrier_closure_statement_join M repA bodyA exA midA resultA HBA HEA HMA HRA)as GOutA.
  pose proof(source_environment_carrier_closure_statement_join M repB bodyB exB midB resultB HBB HEB HMB HRB)as GOutB.
  rewrite(source_environment_carrier_closure_statement_functional M repA outA resultA HOutA GOutA)in POutA.
  rewrite(source_environment_carrier_closure_statement_functional M repB outB resultB HOutB GOutB).
  assert(BA4:source_bounded M repA(code_numeral M 4)).
  { apply(source_bounded_monotone M repA(code_numeral M 2)(code_numeral M 4)BA).
    do 2 apply coding_lt_succ_cancel. apply coding_zero_lt_succ. }
  assert(BB4:source_bounded M repB(code_numeral M 4)).
  { apply(source_bounded_monotone M repB(code_numeral M 2)(code_numeral M 4)BB).
    do 2 apply coding_lt_succ_cancel. apply coding_zero_lt_succ. }
  assert(BMember:source_bounded M(representation_member_code M)(code_numeral M 4)).
  { apply(proj2(source_bounded_accept_atom M SFMember(zeroM M)(code_numeral M 3)
      (representation_member_code M)(code_numeral M 4)(or_introl eq_refl)(sf_make_numeral M SFMember 0 3))).
    split;[apply coding_zero_lt_succ|apply coding_lt_succ]. }
  pose proof(proj2(source_bounded_accept_binary M SFAnd _ _ bodyA(code_numeral M 4)(or_introl eq_refl)HBA)(conj BMember BA4))as BBodyA.
  pose proof(proj2(source_bounded_accept_binary M SFAnd _ _ bodyB(code_numeral M 4)(or_introl eq_refl)HBB)(conj BMember BB4))as BBodyB.
  destruct(sf_relation_total M SFImpl bodyA bodyB)as(bodypoint&HBodyPoint).
  destruct(sf_relation_total M SFImpl exA exB)as(expoint&HExPoint).
  pose proof(source_descriptor_carrier_pair_map M ZFRSourceDescriptor repA repB bodyA bodyB point bodypoint BA BB HBA HBB HPoint HBodyPoint PPoint)as PBody.
  pose proof(source_descriptor_exists_map M ZFRSourceDescriptor bodyA bodyB exA exB bodypoint expoint(code_numeral M 3)
    BBodyA BBodyB HEA HEB HBodyPoint HExPoint PBody)as PEx.
  assert(BS:source_bounded M succ(code_numeral M 3)).
  { apply source_formula_numeral_bounded,representation_successor_finite_bound. }
  assert(BC:source_bounded M closure(code_numeral M 3)).
  { apply source_formula_numeral_bounded,representation_closure_finite_bound. }
  pose proof(proj2(source_bounded_accept_unary M SFEx bodyA exA(code_numeral M 3)(or_intror eq_refl)HEA)BBodyA)as BEA.
  pose proof(proj2(source_bounded_accept_unary M SFEx bodyB exB(code_numeral M 3)(or_intror eq_refl)HEB)BBodyB)as BEB.
  set(env:=fun i=>match i with 0=>succ|1=>closure|2=>exA|_=>exB end).
  assert(P:source_prop_program
    [SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 2));SPTImpl(SPTSlot 2)(SPTSlot 3)]
    (SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 3)))).
  { apply SPTII,SPTII. eapply SPTIE;[apply SPTCtx;cbn;auto|].
    eapply SPTIE;[eapply SPTIE;apply SPTCtx;cbn;auto|apply SPTCtx;cbn;auto]. }
  apply(proj1(source_zfr_descriptor_provable M resultB)).
  apply(source_descriptor_prop_program M ZFRSourceDescriptor _ _ P env(code_numeral M 3)resultB).
  - intros[|[|[|i]]];cbn[env];assumption.
  - intros p[<-|[<-|[]]]f HF.
    + assert(GMA:code_relation M env(source_prop_expression(SPTImpl(SPTSlot 1)(SPTSlot 2)))midA).
      { exact(proj2(schema_expression_graph M env SFImpl(CEvar 1)(CEvar 2)_ _ midA eq_refl eq_refl)HMA). }
      assert(GA:code_relation M env(source_prop_expression(SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 2))))resultA).
      { exact(proj2(schema_expression_graph M env SFImpl(CEvar 0)_ _ _ resultA eq_refl GMA)HRA). }
      rewrite(code_relation_functional M _ env f resultA HF GA).
      exact(proj2(source_zfr_descriptor_provable M resultA)POutA).
    + assert(GE:code_relation M env(source_prop_expression(SPTImpl(SPTSlot 2)(SPTSlot 3)))expoint).
      { exact(proj2(schema_expression_graph M env SFImpl(CEvar 2)(CEvar 3)_ _ expoint eq_refl eq_refl)HExPoint). }
      rewrite(code_relation_functional M _ env f expoint HF GE). exact PEx.
  - assert(GMB:code_relation M env(source_prop_expression(SPTImpl(SPTSlot 1)(SPTSlot 3)))midB).
    { exact(proj2(schema_expression_graph M env SFImpl(CEvar 1)(CEvar 3)_ _ midB eq_refl eq_refl)HMB). }
    exact(proj2(schema_expression_graph M env SFImpl(CEvar 0)_ _ _ resultB eq_refl GMB)HRB).
Qed.
Print Assumptions source_descriptor_carrier_pair_map.
Print Assumptions source_zfr_environment_carrier_closure_map.
