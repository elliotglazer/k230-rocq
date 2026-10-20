(** Actual selected-set existence inside C, from the genuine finite ZFR
    closure certificates. Carrier membership is proved internally. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceBounded NumericalContexts NumericalSourceFull
 SourceLocalDefinabilityContext SourceLocalSelectionExistsGraph SourceLocalDefinabilityContent SourceLocalSelectedSubset
 SourceSelectionOperationGraph SourceNamedQuantifierRules SourceDerivedRules SourceProofWeakening.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Theorem source_full_local_selection_exists M fb fc fn gb gc gn carrier successor closure representative old selected
 succ cl repmem oldmem selectedmem operation body ex k:
 source_local_fixed_context M fb fc fn ->context_included M fb fc fn gb gc gn ->context_bounded M gb gc gn k ->
 code_relation M(local_subset_names carrier successor)source_local_successor_expression succ ->
 code_relation M(local_subset_names successor closure)source_local_closure_expression cl ->
 sf_relation M SFMember representative closure repmem ->sf_relation M SFMember old closure oldmem ->
 (forall i,(i<6)%nat ->selected<>local_selection_exists_roles carrier successor closure representative old i) ->
 sf_relation M SFMember selected closure selectedmem ->
 code_relation M(local_operation5_names representative old carrier selected)source_local_operation5_expression operation ->
 sf_relation M SFAnd selectedmem operation body ->
 code_relation M(local_selection_exists_roles carrier successor closure representative old)source_local_selection_exists_expression ex ->
 source_full_prv M gb gc gn succ ->source_full_prv M gb gc gn cl ->
 source_full_prv M gb gc gn repmem ->source_full_prv M gb gc gn oldmem ->
 source_named_quantifier M false selected body ex /\source_full_prv M gb gc gn ex.
Proof.
 intros HFixed HIncluded BC HS HC HR HE HF HYM HOp HB HX PS PC PR PE.
 split;[exact(source_local_selection_exists_named M carrier successor closure representative old selected selectedmem operation body ex HF HYM HOp HB HX)|].
 destruct(sf_relation_total M SFMember carrier closure)as(ac&HAC).
 destruct(sf_relation_total M SFImpl cl ac)as(cm&HCM).
 destruct(sf_relation_total M SFImpl succ cm)as(carrierlaw&HCL).
 pose proof(source_local_carrier_law_graph M carrier successor closure succ cl ac cm carrierlaw HS HC HAC HCM HCL)as HCarrierGraph.
 pose proof(source_full_local_fixed_instance M fb fc fn 6(fun i=>match i with 0=>carrier|1=>successor|_=>closure end)carrierlaw
  HFixed ltac:(lia)HCarrierGraph)as PAC0.
 pose proof(source_full_prv_weaken_bounded M fb fc fn gb gc gn carrierlaw k PAC0 HIncluded BC)as PAC1.
 pose proof(source_full_modus_ponens M gb gc gn cl ac cm HCM
  (source_full_modus_ponens M gb gc gn succ cm carrierlaw HCL PAC1 PS)PC)as PAC.
 destruct(sf_relation_total M SFImpl ac ex)as(l1&H1).
 destruct(sf_relation_total M SFImpl oldmem l1)as(l2&H2).
 destruct(sf_relation_total M SFImpl repmem l2)as(l3&H3).
 destruct(sf_relation_total M SFImpl cl l3)as(l4&H4).
 destruct(sf_relation_total M SFImpl succ l4)as(law&HL).
 pose proof(source_local_selection_closure_law_graph M carrier successor closure representative old succ cl repmem oldmem ac ex
  l1 l2 l3 l4 law HS HC HR HE HAC HX H1 H2 H3 H4 HL)as HGraph.
 pose proof(source_full_local_fixed_instance M fb fc fn 5(local_selection_exists_roles carrier successor closure representative old)law
  HFixed ltac:(lia)HGraph)as PLaw0.
 pose proof(source_full_prv_weaken_bounded M fb fc fn gb gc gn law k PLaw0 HIncluded BC)as PLaw.
 exact(source_full_modus_ponens M gb gc gn ac ex l1 H1
  (source_full_modus_ponens M gb gc gn oldmem l1 l2 H2
   (source_full_modus_ponens M gb gc gn repmem l2 l3 H3
    (source_full_modus_ponens M gb gc gn cl l3 l4 H4
     (source_full_modus_ponens M gb gc gn succ l4 law HL PLaw PS)PC)PR)PE)PAC).
Qed.
Print Assumptions source_full_local_selection_exists.
