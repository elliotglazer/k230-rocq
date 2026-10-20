(** Close a proof-wide domain table even when it contains more names than
    occur in the conclusion. We first guard-close a widened table, then use
    an actual pure closed implication between the two universal prefixes.
    Domain nonemptiness is used only when relativizing that pure implication. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension CodeExpressions SetFormulaCodes
  SourceBounded SourceBoundedCalibration SourceBoundMonotone SourceTraceBounds NumericalContexts NumericalEnvironments NumericalSourceFull
  NumericalSetClosure ContextCombination SourceClosedContextShift SourceProofWeakening SourceClosedPrefixes
  SourceDomainContexts SourceSequents SourceAxiomContexts SourceDescriptorProvability SourceDescriptorClosure
  SourceRelativization SourceRelativizationBounds SourceGuardedDomainClosure NativeKRelativeBoundary.
Unset Implicit Arguments.

Theorem source_full_closed_prefix_implication M body n m left right out :
  all_prefix M n body left ->all_prefix M m body right ->
  source_bounded M left (zeroM M) ->source_bounded M right (zeroM M) ->
  sf_relation M SFImpl left right out ->
  source_full_prv M (zeroM M)(zeroM M)(zeroM M) out.
Proof.
  intros HL HR HLB HRB HOut.
  destruct(environment_cons_total M (zeroM M)(zeroM M)(zeroM M) left) as(b&c&l&HCons).
  assert(HC:context_bounded M b c l (zeroM M)).
  { apply(proj2(context_bounded_cons M _ _ _ left b c l (zeroM M) HCons)).
    split;[exact HLB|apply context_bounded_empty]. }
  assert(PL:source_full_prv M b c l left).
  { apply full_source_Ctx;[exists(zeroM M);auto|].
    apply(proj2(context_member_cons M _ _ _ left b c l left HCons)). now left. }
  pose proof(source_full_prefix_eliminate M b c l n body left HC HL PL) as PB.
  pose proof(source_full_prefix_introduce M b c l m body right HC HR PB) as PR.
  apply(full_source_II M (zeroM M)(zeroM M)(zeroM M) left right out b c l).
  - exists(zeroM M). split;[|apply context_bounded_empty].
    apply(proj2(source_bounded_accept_binary M SFImpl left right out (zeroM M)
      (or_intror(or_intror eq_refl)) HOut)). auto.
  - exact PR.
  - exact HCons.
  - exact HOut.
Qed.

Theorem source_descriptor_guarded_domain_close_any M T domain ex gb gc gn k m
    body relative result rresult db dc ub uc ul :
  source_axiom_context M T gb gc gn ->source_bounded M domain (code_numeral M 1) ->
  sf_relation M SFEx domain (zeroM M) ex ->source_descriptor_provable M T ex ->
  source_bounded M body m ->all_prefix M m body result ->
  source_relativization M domain body relative ->source_relativization M domain result rresult ->
  source_domain_context M domain k db dc ->context_union M gb gc gn db dc k ub uc ul ->
  source_full_prv M ub uc ul relative ->source_descriptor_provable M T rresult.
Proof.
  intros HG HD HEx PEx HB HP HR HResult HT HU P.
  set(large:=addM M k m).
  assert(HM:coding_lt M m (succM M large)).
  { unfold large. rewrite Arithmetic.add_comm. apply coding_le_add. }
  assert(HK:coding_lt M k (succM M large)) by (unfold large;apply coding_le_add).
  pose proof(source_bounded_monotone M body m large HB HM) as HBodyLarge.
  destruct(source_domain_context_total M domain large) as(lb&lc&HTable).
  destruct(context_union_total M gb gc gn lb lc large) as(vb&vc&vl&HUnion).
  assert(HLarge:context_bounded M vb vc vl large).
  { apply(source_context_union_bounded M gb gc gn lb lc large vb vc vl large HUnion).
    - exact(context_bounded_monotone M gb gc gn (zeroM M) large (proj1 HG)(coding_zero_lt_succ M large)).
    - exact(source_domain_context_bounded M domain large lb lc HD HTable). }
  assert(PBody:source_full_prv M vb vc vl relative).
  { apply(source_full_prv_weaken_bounded M ub uc ul vb vc vl relative large P);[|exact HLarge].
    intros a HA. apply(proj2 HU a) in HA. apply(proj2(proj2 HUnion a)).
    destruct HA as[HA|HA];[now left|right].
    apply(proj1(source_domain_context_member_iff M domain k db dc a HT)) in HA.
    destruct HA as(i&HI&HInst).
    apply(proj2(source_domain_context_member_iff M domain large lb lc a HTable)).
    exists i. split;[|exact HInst].
    destruct(proj1(coding_lt_succ_cases M k large) HK) as[Hlt|E].
    - exact(coding_lt_trans M i k large HI Hlt).
    - now rewrite <-E. }
  destruct(all_prefix_total M large body) as(closedLarge&HClosedLarge).
  destruct(source_relativization_total M domain closedLarge) as(rLarge&HRLarge).
  pose proof(source_full_guarded_domain_close M domain gb gc gn (proj1 HG) HD large
    body relative closedLarge rLarge lb lc vb vc vl HBodyLarge HClosedLarge HR HRLarge HTable HUnion PBody)
    as PLarge.
  pose proof(all_prefix_closes M large body closedLarge HBodyLarge HClosedLarge) as HLargeClosed.
  pose proof(all_prefix_closes M m body result HB HP) as HResultClosed.
  destruct(sf_relation_total M SFImpl closedLarge result) as(imp&HImp).
  pose proof(source_full_closed_prefix_implication M body large m closedLarge result imp
    HClosedLarge HP HLargeClosed HResultClosed HImp) as PPure.
  assert(HImpClosed:source_bounded M imp (zeroM M)).
  { apply(proj2(source_bounded_accept_binary M SFImpl closedLarge result imp (zeroM M)
      (or_intror(or_intror eq_refl)) HImp)). auto. }
  destruct(sf_relation_total M SFImpl rLarge rresult) as(rImp&HRImp).
  assert(HRImpGraph:source_relativization M domain imp rImp).
  { exact(source_relativization_binary M domain SFImpl closedLarge result imp rLarge rresult rImp
      (or_intror(or_intror eq_refl)) HImp HRLarge HResult HRImp). }
  pose proof(source_descriptor_relative_pure_proof M T domain ex imp rImp HD HEx PEx HImpClosed HRImpGraph PPure)
    as PRelative.
  exact(source_descriptor_provable_mp M T rLarge rresult rImp
    (ex_intro _ gb(ex_intro _ gc(ex_intro _ gn(conj HG PLarge)))) PRelative HRImp).
Qed.

Print Assumptions source_full_closed_prefix_implication.
Print Assumptions source_descriptor_guarded_domain_close_any.
