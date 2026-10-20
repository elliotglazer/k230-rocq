(** Consume actual axiom-image proofs and a proof of domain nonemptiness.
    This is a source proof construction inside every PA model. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  NumericalContexts NumericalInstantiation SourceBounded SourceBoundMonotone
  SourceSequents SourceTraceBounds SetFormulaCodes NumericalSourceFull ContextCombination
  SourceContextTransport SourceProofWeakening SourceHypothesisTransport
  SourceRelativization SourceRelativeContexts SourceRelativeFullTranslation
  SourceDomainContexts SourceClosedContextShift SourceAmbientDomainDischarge.
Unset Implicit Arguments.

Theorem source_relative_proof_transfer M domain ex gb gc gn sb sc sn f rf :
  context_bounded M gb gc gn (zeroM M) ->
  source_bounded M domain (code_numeral M 1) ->
  sf_relation M SFEx domain (zeroM M) ex -> source_full_prv M gb gc gn ex ->
  source_bounded M rf (zeroM M) -> source_relativization M domain f rf ->
  (forall a ra,context_member M sb sc sn a -> source_relativization M domain a ra ->
    source_full_prv M gb gc gn ra) ->
  source_full_prv M sb sc sn f -> source_full_prv M gb gc gn rf.
Proof.
  intros HClosed HD HEx PEx HRF HRel HA HP.
  destruct (source_full_relativized_proof M domain HD sb sc sn f HP) as [bound HTranslate].
  destruct (source_relative_context_total M domain sb sc sn bound) as [b [c [n HC]]].
  pose proof (HTranslate bound b c n rf (coding_lt_succ M bound) HC HRel) as PRel.
  destruct (source_domain_context_total M domain bound) as [db [dc HTable]].
  destruct (context_union_total M gb gc gn db dc bound) as [ub [uc [un HU]]].
  assert (HUbound:context_bounded M ub uc un bound).
  { apply (source_context_union_bounded M gb gc gn db dc bound ub uc un bound HU).
    - exact (context_bounded_monotone M gb gc gn (zeroM M) bound HClosed (coding_zero_lt_succ M bound)).
    - exact (source_domain_context_bounded M domain bound db dc HD HTable). }
  apply (source_ambient_domain_table_discharge M domain ex rf gb gc gn
    HClosed HD HEx PEx HRF bound db dc ub uc un HTable HU).
  apply (source_full_prv_replace_hypotheses M ub uc un (ex_intro _ bound HUbound) n b c rf PRel).
  intros a HMember.
  apply (proj1 (source_relative_context_member_iff M domain sb sc sn bound b c n a HC)) in HMember.
  destruct HMember as [[h [HH HR]]|HDom].
  - apply (source_full_prv_weaken_bounded M gb gc gn ub uc un a bound (HA h a HH HR)).
    + exact (context_union_left M gb gc gn db dc bound ub uc un HU).
    + exact HUbound.
  - assert (HM:context_member M ub uc un a).
    { apply (context_union_right M gb gc gn db dc bound ub uc un HU).
      exact (proj2 (source_domain_context_member_iff M domain bound db dc a HTable) HDom). }
    apply full_source_Ctx;[|exact HM]. exists bound. split;[exact (HUbound a HM)|exact HUbound].
Qed.

Corollary source_relative_refutation_transfer M domain ex gb gc gn sb sc sn :
  context_bounded M gb gc gn (zeroM M) ->
  source_bounded M domain (code_numeral M 1) ->
  sf_relation M SFEx domain (zeroM M) ex -> source_full_prv M gb gc gn ex ->
  (forall a ra,context_member M sb sc sn a -> source_relativization M domain a ra ->
    source_full_prv M gb gc gn ra) ->
  source_full_prv M sb sc sn (zeroM M) -> source_full_prv M gb gc gn (zeroM M).
Proof.
  intros HClosed HD HEx PEx HA HP.
  exact (source_relative_proof_transfer M domain ex gb gc gn sb sc sn (zeroM M) (zeroM M)
    HClosed HD HEx PEx (source_bounded_accept_falsity M (zeroM M))
    (source_relativization_falsity M domain) HA HP).
Qed.

Print Assumptions source_relative_proof_transfer.
Print Assumptions source_relative_refutation_transfer.
