(** Universal TV from the positive child induction hypothesis alone.
    Negative equivalence and all auxiliary code graphs are constructed. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  NumericalContexts NumericalSourceFull SourceRelativizationRules SourceIffGraphs
  SourceGuardedNegatedEquivalence SourceTarskiVaughtAll.
Unset Implicit Arguments.
Definition source_tv_negative_closure M domain carrier a closure:=exists negA exDomain exCarrier,
  sf_relation M SFImpl a(zeroM M)negA /\sr_quantifier M false domain negA exDomain /\
  sr_quantifier M false carrier negA exCarrier /\sf_relation M SFImpl exDomain exCarrier closure.

Theorem source_full_tv_all_forward_from_positive M cb cc cn domain carrier a b equiv point ih
    subsetPoint subset allDomain allCarrier k:
  context_bounded M cb cc cn k ->source_bounded M domain(succM M k) ->source_bounded M carrier(succM M k) ->
  source_bounded M a(succM M k) ->source_bounded M b(succM M k) ->
  source_iff_graph M a b equiv ->sf_relation M SFImpl carrier equiv point ->sf_relation M SFAll point(zeroM M)ih ->
  sf_relation M SFImpl carrier domain subsetPoint ->sf_relation M SFAll subsetPoint(zeroM M)subset ->
  sr_quantifier M true domain a allDomain ->sr_quantifier M true carrier b allCarrier ->
  source_full_prv M cb cc cn ih ->source_full_prv M cb cc cn subset ->source_full_prv M cb cc cn allDomain ->
  source_full_prv M cb cc cn allCarrier.
Proof.
  intros BC BD BG BA BB HI HP HQ HS HQS HD HU PI PS PD.
  destruct(sf_relation_total M SFImpl a(zeroM M))as(negA&HNA).
  destruct(sf_relation_total M SFImpl b(zeroM M))as(negB&HNB).
  destruct(source_iff_total M negA negB)as(negEquiv&HNI).
  destruct(sf_relation_total M SFImpl carrier negEquiv)as(negPoint&HNP).
  destruct(sf_relation_total M SFAll negPoint(zeroM M))as(negIH&HNQ).
  pose proof(source_full_guarded_negated_equivalence M cb cc cn carrier a b equiv point ih negA negB negEquiv negPoint negIH k
    BC BG BA BB HI HP HQ HNA HNB HNI HNP HNQ PI)as PNI.
  destruct(sr_quantifier_total M false domain negA)as(exD&HExD).
  destruct(sr_quantifier_total M false carrier negA)as(exA&HExA).
  destruct(sr_quantifier_total M false carrier negB)as(exB&HExB).
  exact(source_full_tv_all_forward M cb cc cn domain carrier a b negA negB negEquiv negPoint negIH subsetPoint subset
    exD exA exB allDomain allCarrier k BC BD BG BA BB HNA HNB HNI HNP HNQ HS HQS HExD HExA HExB HD HU PNI PS PD).
Qed.

Theorem source_full_tv_all_reverse_from_positive M cb cc cn domain carrier a b equiv point ih
    closure allDomain allCarrier k:
  context_bounded M cb cc cn k ->source_bounded M domain(succM M k) ->source_bounded M carrier(succM M k) ->
  source_bounded M a(succM M k) ->source_bounded M b(succM M k) ->
  source_iff_graph M a b equiv ->sf_relation M SFImpl carrier equiv point ->sf_relation M SFAll point(zeroM M)ih ->
  source_tv_negative_closure M domain carrier a closure ->
  sr_quantifier M true domain a allDomain ->sr_quantifier M true carrier b allCarrier ->
  source_full_prv M cb cc cn ih ->source_full_prv M cb cc cn closure ->source_full_prv M cb cc cn allCarrier ->
  source_full_prv M cb cc cn allDomain.
Proof.
  intros BC BD BG BA BB HI HP HQ(negA&exD&exA&HNA&HExD&HExA&HC)HD HU PI PC PU.
  destruct(sf_relation_total M SFImpl b(zeroM M))as(negB&HNB).
  destruct(source_iff_total M negA negB)as(negEquiv&HNI).
  destruct(sf_relation_total M SFImpl carrier negEquiv)as(negPoint&HNP).
  destruct(sf_relation_total M SFAll negPoint(zeroM M))as(negIH&HNQ).
  pose proof(source_full_guarded_negated_equivalence M cb cc cn carrier a b equiv point ih negA negB negEquiv negPoint negIH k
    BC BG BA BB HI HP HQ HNA HNB HNI HNP HNQ PI)as PNI.
  destruct(sr_quantifier_total M false carrier negB)as(exB&HExB).
  exact(source_full_tv_all_reverse M cb cc cn domain carrier a b negA negB negEquiv negPoint negIH
    exD exA exB closure allDomain allCarrier k BC BD BG BA BB HNA HNB HNI HNP HNQ HExD HExA HExB HC HD HU PNI PC PU).
Qed.
Print Assumptions source_full_tv_all_forward_from_positive.
Print Assumptions source_full_tv_all_reverse_from_positive.
