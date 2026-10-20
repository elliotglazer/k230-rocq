(** Actual finite extension-existence proof in every bounded extension
    of the fixed local-definability background context. *)
From Stdlib Require Import Lia.
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceBounded NumericalContexts NumericalSourceFull
 SourceLocalDefinabilityContext SourceProjectionExtensionBinder SourceProjectionOperationFixed
 SourceEnvInClosureConstructor SourceNamedQuantifierRules SourceProofWeakening.
Unset Implicit Arguments.
Theorem source_full_local_extension_exists M fb fc fn gb gc gn old value witness extension k:
 source_local_fixed_context M fb fc fn ->context_included M fb fc fn gb gc gn ->
 context_bounded M gb gc gn k ->witness<>old ->witness<>value ->
 code_relation M(EIC_ext_roles old witness value)EIC_ext_expression extension ->
 exists ex,source_named_quantifier M false witness extension ex /\source_full_prv M gb gc gn ex.
Proof.
 intros HFixed HIncluded BC WO WV HExt.
 destruct(code_relation_total M source_projection_extension_expression(projection_two_values old value))as(ex&HEx).
 exists ex. split.
 - exact(source_projection_extension_named_exists M old value witness extension ex WO WV HExt HEx).
 - apply(source_full_prv_weaken_bounded M fb fc fn gb gc gn ex k);try assumption.
   exact(source_full_local_fixed_instance M fb fc fn 4(projection_two_values old value)ex HFixed ltac:(lia)HEx).
Qed.
Print Assumptions source_full_local_extension_exists.
