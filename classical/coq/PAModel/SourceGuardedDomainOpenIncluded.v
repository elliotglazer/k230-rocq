(** Open a genuine guarded source prefix in any bounded context containing
    both its closed proof background and its exact finite domain table. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SourceBounded
 NumericalContexts NumericalSetClosure NumericalSourceFull SourceRelativization
 SourceDomainContexts SourceGuardedDomainOpening SourceProofWeakening ContextCombination.
Unset Implicit Arguments.

Theorem source_full_guarded_domain_open_included M domain gb gc gn count body relative f rf db dc b c l k :
 context_bounded M gb gc gn (zeroM M) ->
 source_bounded M domain (code_numeral M 1) -> source_bounded M body count ->
 all_prefix M count body f ->
 source_relativization M domain body relative -> source_relativization M domain f rf ->
 source_domain_context M domain count db dc ->
 context_included M gb gc gn b c l -> context_included M db dc count b c l ->
 context_bounded M b c l k -> source_full_prv M gb gc gn rf ->
 source_full_prv M b c l relative.
Proof.
 intros HClosed HD HB HP HR HF HT HBase HTable HC P.
 destruct (context_union_total M gb gc gn db dc count) as (ub&uc&un&HU).
 pose proof (source_full_guarded_domain_open M domain gb gc gn HClosed HD
   count body relative f rf db dc ub uc un HB HP HR HF HT HU P) as POpen.
 apply (source_full_prv_weaken_bounded M ub uc un b c l relative k POpen); [|exact HC].
 intros a HA. apply (proj1 (proj2 HU a)) in HA.
 destruct HA as [HA|HA]; [exact (HBase a HA)|exact (HTable a HA)].
Qed.

Print Assumptions source_full_guarded_domain_open_included.
