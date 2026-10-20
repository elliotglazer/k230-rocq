(** The actual universal Tarski-Vaught step, using the negative child
    equivalence and witness closure. This constructs ordinary source proofs;
    no truth predicate or semantic completeness principle occurs. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  NumericalContexts NumericalEnvironments NumericalSourceFull SourceRelativizationRules SourceIffGraphs
  SourceD0Recipe SourceContextProofHelpers SourceDerivedRules SourceQuantifierRules
  SourceGuardedQuantifierDuality SourceTarskiVaughtExists.
Unset Implicit Arguments.

Theorem source_full_tv_all_forward M cb cc cn domain carrier a b negA negB negEquiv point ih
    subsetPoint subset exDomain exCarrierA exCarrierB allDomain allCarrier k:
  context_bounded M cb cc cn k ->source_bounded M domain(succM M k) ->source_bounded M carrier(succM M k) ->
  source_bounded M a(succM M k) ->source_bounded M b(succM M k) ->
  sf_relation M SFImpl a(zeroM M)negA ->sf_relation M SFImpl b(zeroM M)negB ->
  source_iff_graph M negA negB negEquiv ->sf_relation M SFImpl carrier negEquiv point ->sf_relation M SFAll point(zeroM M)ih ->
  sf_relation M SFImpl carrier domain subsetPoint ->sf_relation M SFAll subsetPoint(zeroM M)subset ->
  sr_quantifier M false domain negA exDomain ->sr_quantifier M false carrier negA exCarrierA ->sr_quantifier M false carrier negB exCarrierB ->
  sr_quantifier M true domain a allDomain ->sr_quantifier M true carrier b allCarrier ->
  source_full_prv M cb cc cn ih ->source_full_prv M cb cc cn subset ->source_full_prv M cb cc cn allDomain ->
  source_full_prv M cb cc cn allCarrier.
Proof.
  intros BC BD BG BA BB HNA HNB HNI HP HI HS HQS HD HA HB HAllD HAllU PI PS PD.
  pose proof(proj2(source_bounded_accept_binary M SFImpl a(zeroM M)negA(succM M k)(or_intror(or_intror eq_refl))HNA)
    (conj BA(source_bounded_accept_falsity M(succM M k))))as BNA.
  pose proof(proj2(source_bounded_accept_binary M SFImpl b(zeroM M)negB(succM M k)(or_intror(or_intror eq_refl))HNB)
    (conj BB(source_bounded_accept_falsity M(succM M k))))as BNB.
  pose proof(source_guarded_exists_bounded M carrier negB exCarrierB k BG BNB HB)as BExU.
  destruct HAllD as(dpoint&HDP&HDA). destruct HAllU as(upoint&HUP&HUA).
  pose proof HD as HD0. destruct HD0 as(dbody&HDB&HDE).
  pose proof HB as HB0. destruct HB0 as(ubody&HUB&HUE).
  destruct(sf_relation_total M SFImpl exDomain(zeroM M))as(notD&HNotD).
  destruct(sf_relation_total M SFImpl exCarrierB(zeroM M))as(notU&HNotU).
  pose proof(source_full_not_exists_neg_from_guarded_all M cb cc cn domain a dpoint negA dbody exDomain notD allDomain k
    BC BD BA HDP HNA HDB HDE HNotD HDA PD)as PNotD.
  pose proof(proj2(source_bounded_accept_binary M SFImpl exCarrierB(zeroM M)notU k(or_intror(or_intror eq_refl))HNotU)
    (conj BExU(source_bounded_accept_falsity M k)))as BNotU.
  destruct(environment_cons_total M cb cc cn exCarrierB)as(ub&uc&un&HCons).
  pose proof(proj2(context_bounded_cons M cb cc cn exCarrierB ub uc un k HCons)(conj BExU BC))as BU.
  pose proof(source_full_cons_head M cb cc cn exCarrierB ub uc un k HCons BExU BU)as PExU.
  pose proof(source_full_cons_weaken M cb cc cn exCarrierB ub uc un k ih HCons BU PI)as PIU.
  pose proof(source_full_cons_weaken M cb cc cn exCarrierB ub uc un k subset HCons BU PS)as PSU.
  pose proof(source_full_cons_weaken M cb cc cn exCarrierB ub uc un k notD HCons BU PNotD)as PNDU.
  pose proof(source_full_tv_exists_reverse M ub uc un domain carrier negA negB negEquiv point ih subsetPoint subset
    exDomain exCarrierA exCarrierB k BU BD BG BNA BNB HNI HP HI HS HQS HD HA HB PIU PSU PExU)as PExD.
  pose proof(source_full_modus_ponens M ub uc un exDomain(zeroM M)notD HNotD PNDU PExD)as PFalse.
  pose proof(full_source_II M cb cc cn exCarrierB(zeroM M)notU ub uc un(ex_intro _ k(conj BNotU BC))PFalse HCons HNotU)as PNotU.
  exact(source_full_guarded_all_from_not_exists_neg M cb cc cn carrier b upoint negB ubody exCarrierB notU allCarrier k
    BC BG BB HUP HNB HUB HUE HNotU HUA PNotU).
Qed.

Theorem source_full_tv_all_reverse M cb cc cn domain carrier a b negA negB negEquiv point ih
    exDomain exCarrierA exCarrierB closure allDomain allCarrier k:
  context_bounded M cb cc cn k ->source_bounded M domain(succM M k) ->source_bounded M carrier(succM M k) ->
  source_bounded M a(succM M k) ->source_bounded M b(succM M k) ->
  sf_relation M SFImpl a(zeroM M)negA ->sf_relation M SFImpl b(zeroM M)negB ->
  source_iff_graph M negA negB negEquiv ->sf_relation M SFImpl carrier negEquiv point ->sf_relation M SFAll point(zeroM M)ih ->
  sr_quantifier M false domain negA exDomain ->sr_quantifier M false carrier negA exCarrierA ->sr_quantifier M false carrier negB exCarrierB ->
  sf_relation M SFImpl exDomain exCarrierA closure ->
  sr_quantifier M true domain a allDomain ->sr_quantifier M true carrier b allCarrier ->
  source_full_prv M cb cc cn ih ->source_full_prv M cb cc cn closure ->source_full_prv M cb cc cn allCarrier ->
  source_full_prv M cb cc cn allDomain.
Proof.
  intros BC BD BG BA BB HNA HNB HNI HP HI HD HA HB HC HAllD HAllU PI PC PU.
  pose proof(proj2(source_bounded_accept_binary M SFImpl a(zeroM M)negA(succM M k)(or_intror(or_intror eq_refl))HNA)
    (conj BA(source_bounded_accept_falsity M(succM M k))))as BNA.
  pose proof(proj2(source_bounded_accept_binary M SFImpl b(zeroM M)negB(succM M k)(or_intror(or_intror eq_refl))HNB)
    (conj BB(source_bounded_accept_falsity M(succM M k))))as BNB.
  pose proof(source_guarded_exists_bounded M domain negA exDomain k BD BNA HD)as BExD.
  destruct HAllD as(dpoint&HDP&HDA). destruct HAllU as(upoint&HUP&HUA).
  pose proof HD as HD0. destruct HD0 as(dbody&HDB&HDE).
  pose proof HB as HB0. destruct HB0 as(ubody&HUB&HUE).
  destruct(sf_relation_total M SFImpl exDomain(zeroM M))as(notD&HNotD).
  destruct(sf_relation_total M SFImpl exCarrierB(zeroM M))as(notU&HNotU).
  pose proof(source_full_not_exists_neg_from_guarded_all M cb cc cn carrier b upoint negB ubody exCarrierB notU allCarrier k
    BC BG BB HUP HNB HUB HUE HNotU HUA PU)as PNotU.
  pose proof(proj2(source_bounded_accept_binary M SFImpl exDomain(zeroM M)notD k(or_intror(or_intror eq_refl))HNotD)
    (conj BExD(source_bounded_accept_falsity M k)))as BNotD.
  destruct(environment_cons_total M cb cc cn exDomain)as(ub&uc&un&HCons).
  pose proof(proj2(context_bounded_cons M cb cc cn exDomain ub uc un k HCons)(conj BExD BC))as BU.
  pose proof(source_full_cons_head M cb cc cn exDomain ub uc un k HCons BExD BU)as PExD.
  pose proof(source_full_cons_weaken M cb cc cn exDomain ub uc un k ih HCons BU PI)as PIU.
  pose proof(source_full_cons_weaken M cb cc cn exDomain ub uc un k closure HCons BU PC)as PCU.
  pose proof(source_full_cons_weaken M cb cc cn exDomain ub uc un k notU HCons BU PNotU)as PNUU.
  pose proof(source_full_tv_exists_forward M ub uc un domain carrier negA negB negEquiv point ih
    exDomain exCarrierA exCarrierB closure k BU BG BNA BNB HNI HP HI HD HA HB HC PIU PCU PExD)as PExU.
  pose proof(source_full_modus_ponens M ub uc un exCarrierB(zeroM M)notU HNotU PNUU PExU)as PFalse.
  pose proof(full_source_II M cb cc cn exDomain(zeroM M)notD ub uc un(ex_intro _ k(conj BNotD BC))PFalse HCons HNotD)as PNotD.
  exact(source_full_guarded_all_from_not_exists_neg M cb cc cn domain a dpoint negA dbody exDomain notD allDomain k
    BC BD BA HDP HNA HDB HDE HNotD HDA PNotD).
Qed.
Print Assumptions source_full_tv_all_forward.
Print Assumptions source_full_tv_all_reverse.
