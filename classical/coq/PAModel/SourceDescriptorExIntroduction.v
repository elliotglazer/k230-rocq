(** Actual source proof of instance -> existence, with arbitrary internal syntax. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
 SourceBounded SourceSequents SourceTraceBounds NumericalContexts NumericalEnvironments
 NumericalInstantiation NumericalSourceFull SourceDescriptorProvability SourceDescriptorClosure
 SourceContextProofHelpers.
Unset Implicit Arguments.
Theorem source_descriptor_ex_introduction M T body ex name instance implication k :
 source_bounded M ex k ->source_bounded M instance k ->
 sf_relation M SFEx body(zeroM M)ex ->numerical_instantiation M body name instance ->
 sf_relation M SFImpl instance ex implication ->source_descriptor_provable M T implication.
Proof.
 intros BEx BInstance HEx HInstance HImp.
 destruct(environment_cons_total M(zeroM M)(zeroM M)(zeroM M)instance)as(b&c&n&HCons).
 assert(HC:context_bounded M b c n k).
 { exact(proj2(context_bounded_cons M _ _ _ instance b c n k HCons)(conj BInstance(context_bounded_empty M(zeroM M)(zeroM M) k))). }
 apply source_descriptor_provable_from_empty.
 apply(full_source_II M _ _ _ instance ex implication b c n).
 - exists k. split;[|apply context_bounded_empty].
   exact(proj2(source_bounded_accept_binary M SFImpl instance ex implication k(or_intror(or_intror eq_refl))HImp)(conj BInstance BEx)).
 - apply(full_source_ExI M b c n body ex name instance).
   + exists k. auto.
   + exact(source_full_cons_head M _ _ _ instance b c n k HCons BInstance HC).
   + exact HEx.
   + exact HInstance.
 - exact HCons.
 - exact HImp.
Qed.
Print Assumptions source_descriptor_ex_introduction.
