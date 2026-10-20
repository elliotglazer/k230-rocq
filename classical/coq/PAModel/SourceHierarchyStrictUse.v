(** Apply strict LL monotonicity using five actual local proofs. The result
    explicitly returns the finite closed ZFR context it adds. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 SourceHierarchyStrictShell SourceHierarchySyntax SourceRawSubset SourcePHHierarchyOrdinals
 SourceOrdinalPredicate NumericalInstantiation NumericalContexts NumericalSourceFull ContextCombination
 SourceZFRProvability SourceProofWeakening SourceTraceBounds SourceFiniteTelescope
 SourceContextTransport SourceConjunctionRules SourceClosedContextShift.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_full_hierarchy_strict M d e u v od oe member ld le inLevel subset gb gc gn k:
 context_bounded M gb gc gn k ->
 numerical_instantiation M(source_ordinal_predicate_code M)d od ->
 numerical_instantiation M(source_ordinal_predicate_code M)e oe ->
 sf_relation M SFMember d e member ->source_LL_instance M d u ld ->source_LL_instance M e v le ->
 sf_relation M SFMember u v inLevel ->source_raw_subset_graph M u v subset ->
 source_full_prv M gb gc gn od ->source_full_prv M gb gc gn oe ->source_full_prv M gb gc gn member ->
 source_full_prv M gb gc gn ld ->source_full_prv M gb gc gn le ->
 exists nb nc nn ub uc un,source_zfr_context M nb nc nn /\context_union M gb gc gn nb nc nn ub uc un /\
 source_full_prv M ub uc un inLevel /\source_full_prv M ub uc un subset.
Proof.
 intros BC HOD HOE HM HLD HLE HMember HSubset POD POE PM PLD PLE.
 destruct(source_zfr_hierarchy_strict_shell M d e u v)
  as(od'&oe'&member'&ld'&le'&inLevel'&subset'&pair&law&HOD'&HOE'&HM'&HLD'&HLE'&HMember'&HSubset'&HPair&HT&PLaw).
 pose proof(numerical_instantiation_functional M _ d od od' HOD HOD')as E;subst od'.
 pose proof(numerical_instantiation_functional M _ e oe oe' HOE HOE')as E;subst oe'.
 pose proof(sf_relation_functional M SFMember d e member member' HM HM')as E;subst member'.
 pose proof(source_LL_instance_functional M d u ld ld' HLD HLD')as E;subst ld'.
 pose proof(source_LL_instance_functional M e v le le' HLE HLE')as E;subst le'.
 pose proof(sf_relation_functional M SFMember u v inLevel inLevel' HMember HMember')as E;subst inLevel'.
 pose proof(source_PH_raw_subset_functional M u v subset subset' HSubset HSubset')as E;subst subset'.
 destruct PLaw as(nb&nc&nn&HNC&PLaw).
 destruct(context_union_total M gb gc gn nb nc nn)as(ub&uc&un&HU).
 pose proof(source_zfr_context_closed M nb nc nn HNC)as BN0.
 pose proof(context_bounded_monotone M nb nc nn(zeroM M)k BN0(coding_zero_lt_succ M k))as BN.
 pose proof(source_context_union_bounded M gb gc gn nb nc nn ub uc un k HU BC BN)as BU.
 pose proof(source_full_prv_weaken_bounded M nb nc nn ub uc un law k PLaw
  (context_union_right M gb gc gn nb nc nn ub uc un HU)BU)as PNewLaw.
 assert(HWeaken:forall f,source_full_prv M gb gc gn f ->source_full_prv M ub uc un f).
 { intros f PF. exact(source_full_prv_weaken_bounded M gb gc gn ub uc un f k PF
    (context_union_left M gb gc gn nb nc nn ub uc un HU)BU). }
 assert(PPair:source_full_prv M ub uc un pair).
 { apply(source_full_finite_telescope_apply M[od;oe;member;ld;le]pair law HT ub uc un PNewLaw).
   intros a HA. simpl in HA. destruct HA as[<-|[<-|[<-|[<-|[<-|[]]]]]];apply HWeaken;assumption. }
 exists nb,nc,nn,ub,uc,un. split;[exact HNC|]. split;[exact HU|]. split.
 - exact(source_full_conjunction_left M ub uc un inLevel subset pair HPair PPair).
 - exact(source_full_conjunction_right M ub uc un inLevel subset pair HPair PPair).
Qed.
Print Assumptions source_full_hierarchy_strict.
