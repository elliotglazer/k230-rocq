(** The actual existential Tarski-Vaught step. Forward uses witness
    closure; reverse uses carrier containment. Child equivalence is an
    ordinary universally guarded source proof. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  NumericalContexts NumericalSourceFull SourceRelativizationRules SourceIffGraphs SourceDerivedRules
  SourceGuardedExistsCongruence SourceGuardedExistsGuardMap.
Unset Implicit Arguments.
Theorem source_full_tv_exists_forward M cb cc cn domain carrier a b equiv point ih exDomain exCarrierA exCarrierB closure k:
  context_bounded M cb cc cn k ->source_bounded M carrier(succM M k) ->
  source_bounded M a(succM M k) ->source_bounded M b(succM M k) ->
  source_iff_graph M a b equiv ->sf_relation M SFImpl carrier equiv point ->sf_relation M SFAll point(zeroM M)ih ->
  sr_quantifier M false domain a exDomain ->sr_quantifier M false carrier a exCarrierA ->
  sr_quantifier M false carrier b exCarrierB ->sf_relation M SFImpl exDomain exCarrierA closure ->
  source_full_prv M cb cc cn ih ->source_full_prv M cb cc cn closure ->source_full_prv M cb cc cn exDomain ->
  source_full_prv M cb cc cn exCarrierB.
Proof.
  intros BC BG BA BB HI HP HQ HD HA HB HC PI PC PD.
  pose proof(source_full_modus_ponens M cb cc cn exDomain exCarrierA closure HC PC PD)as PA.
  exact(source_full_guarded_exists_congruence M cb cc cn false carrier a b equiv point ih exCarrierA exCarrierB k
    BC BG BA BB HI HP HQ HA HB PI PA).
Qed.
Theorem source_full_tv_exists_reverse M cb cc cn domain carrier a b equiv point ih subsetPoint subset exDomain exCarrierA exCarrierB k:
  context_bounded M cb cc cn k ->source_bounded M domain(succM M k) ->source_bounded M carrier(succM M k) ->
  source_bounded M a(succM M k) ->source_bounded M b(succM M k) ->
  source_iff_graph M a b equiv ->sf_relation M SFImpl carrier equiv point ->sf_relation M SFAll point(zeroM M)ih ->
  sf_relation M SFImpl carrier domain subsetPoint ->sf_relation M SFAll subsetPoint(zeroM M)subset ->
  sr_quantifier M false domain a exDomain ->sr_quantifier M false carrier a exCarrierA ->sr_quantifier M false carrier b exCarrierB ->
  source_full_prv M cb cc cn ih ->source_full_prv M cb cc cn subset ->source_full_prv M cb cc cn exCarrierB ->
  source_full_prv M cb cc cn exDomain.
Proof.
  intros BC BD BG BA BB HI HP HQ HS HQS HD HA HB PI PS PB.
  pose proof(source_full_guarded_exists_congruence M cb cc cn true carrier a b equiv point ih exCarrierB exCarrierA k
    BC BG BA BB HI HP HQ HB HA PI PB)as PA.
  exact(source_full_guarded_exists_guard_map M cb cc cn carrier domain a subsetPoint subset exCarrierA exDomain k
    BC BG BD BA HS HQS HA HD PS PA).
Qed.
Print Assumptions source_full_tv_exists_forward.
Print Assumptions source_full_tv_exists_reverse.
