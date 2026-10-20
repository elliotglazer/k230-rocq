(** Actual arbitrary-hole An head proof. The finite Op3 theorem and all
    source-calculus quantifier inferences are discharged internally; the
    remaining premises are explicit syntax/bound/eigenname graphs. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceBounded SourcePropositionalTemplates
 SourceDescriptorProvability SourceDescriptorPrograms SourceZFRProvability SourceSetTheoryDescriptors
 SourceEnvironmentPointSlots SourceEnvironmentCarrierFixed SourceEnvironmentExtensionProgram
 SourceEnvironmentExtensionQuantifiers SourceNamedVacuity SourceNamedQuantifierRules.
Unset Implicit Arguments.
Theorem source_zfr_environment_head_proof M rho values witness e a previousbody newbody localbody headbody result k:
 (forall i,source_bounded M(values i)k) ->
 (forall i,(i<5)%nat ->code_relation M rho(environment_extension_fixed_slot i)(values i)) ->
 code_relation M values(source_prop_expression(SPTImpl(SPTSlot 5)(SPTSlot 1)))previousbody ->
 code_relation M values(source_prop_expression(SPTAnd(SPTSlot 5)(SPTSlot 3)))newbody ->
 code_relation M values(source_prop_expression environment_extension_local_body)localbody ->
 code_relation M values(source_prop_expression environment_extension_head_body)headbody ->
 source_named_quantifier M true witness previousbody(values 6) ->
 source_named_quantifier M false witness newbody(values 7) ->
 source_named_quantifier M true e localbody(values 8) ->
 source_named_quantifier M true a headbody(values 9) ->
 source_named_vacuous M witness(values 0) ->source_named_vacuous M witness(values 2) ->
 source_named_vacuous M witness(values 4) ->
 source_named_vacuous M e(values 0) ->source_named_vacuous M e(values 6) ->source_named_vacuous M e(values 2) ->
 source_named_vacuous M a(values 0) ->source_named_vacuous M a(values 6) ->
 code_relation M values(source_prop_expression environment_extension_all_result)result ->source_zfr_provable M result.
Proof.
 intros HB HSlots HPrevious HNew HLocal HHead HAll HEx HE HA VP0 VP2 VP4 VE0 VE6 VE2 VA0 VA6 HResult.
 destruct(code_relation_total M source_environment_extension_point_expression rho)as(law&HFixed).
 pose proof(proj1(source_environment_extension_fixed_slots_prefix M rho values law HSlots)HFixed)as HLaw.
 apply(proj1(source_zfr_descriptor_provable M result)).
 apply(source_descriptor_environment_extension_quantifiers M ZFRSourceDescriptor values e a localbody headbody result k
  HB HLocal HHead HE HA VE0 VE6 VE2 VA0 VA6);[|exact HResult].
 intros f HF. apply(proj2(source_zfr_descriptor_provable M f)).
 exact(source_zfr_environment_extension M rho values witness previousbody newbody law f k HB HPrevious HNew
  HAll HEx VP0 VP2 VP4 HFixed HLaw HF).
Qed.
Print Assumptions source_zfr_environment_head_proof.
