(** Guarded universal introduction under an ordinary outer condition,
    using actual source proofs in closed ZFR axiom contexts. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourceTraceBounds
  NumericalContexts NumericalEnvironments NumericalContextRenaming NumericalSourceFull NumericalRenaming
  SourceQuantifierRules SourceClosedPrefixes SourceClosedContextShift SourceUniversalPropositional SourceProofWeakening SourceProofRenaming
  SourceLeastOrdinalWitness SourceDerivedRules SourceDescriptorProvability SourceZFRProvability.
Unset Implicit Arguments.

Theorem source_zfr_cb_all_intro M condition shifted guard conclusion point all pointImp result k:
  source_bounded M condition k ->source_bounded M guard(succM M k) ->source_bounded M conclusion(succM M k) ->
  source_formula_shift M condition shifted ->sf_relation M SFImpl guard conclusion point ->
  sf_relation M SFAll point(zeroM M)all ->sf_relation M SFImpl shifted conclusion pointImp ->
  sf_relation M SFImpl condition all result ->source_zfr_provable M pointImp ->source_zfr_provable M result.
Proof.
  intros HB HG HC HS HP HA HPI HR(b&c&n&HCtx&PP).
  pose proof(proj2(source_zfr_descriptor_context M b c n)HCtx) as HAx.
  pose proof(context_bounded_monotone M b c n(zeroM M)k(proj1 HAx)(coding_zero_lt_succ M k)) as HCtxB.
  assert(HPointB:source_bounded M point(succM M k)).
  { exact(proj2(source_bounded_accept_binary M SFImpl guard conclusion point(succM M k)
      (or_intror(or_intror eq_refl))HP)(conj HG HC)). }
  assert(HAllB:source_bounded M all k).
  { exact(proj2(source_bounded_accept_unary M SFAll point all k(or_introl eq_refl)HA)HPointB). }
  destruct(sf_relation_total M SFAll pointImp(zeroM M)) as(allImp&HAI).
  pose proof(source_full_all_intro_closed M b c n pointImp allImp(proj1 HAx)HAI PP) as PAllImp.
  destruct(environment_cons_total M b c n condition) as(pb&pc&pn&HConsP).
  assert(HPCtx:context_bounded M pb pc pn k).
  { exact(proj2(context_bounded_cons M b c n condition pb pc pn k HConsP)(conj HB HCtxB)). }
  assert(PCondition:source_full_prv M pb pc pn condition).
  { apply full_source_Ctx;[exists k;auto|].
    apply(proj2(context_member_cons M b c n condition pb pc pn condition HConsP)). now left. }
  pose proof(source_full_prv_weaken_bounded M b c n pb pc pn allImp k PAllImp
    (source_cons_tail_inclusion M b c n condition pb pc pn HConsP)HPCtx) as PAllImpP.
  destruct(context_shift_total M pb pc pn) as(sb&sc&HShift).
  pose proof(context_shift_preserves_bound M pb pc pn sb sc k HShift HPCtx) as HShiftB.
  pose proof(source_full_all_shift M pb pc pn pointImp allImp sb sc HAI PAllImpP HShift) as PPointImp.
  pose proof(source_full_prv_renaming M pb pc pn condition(zeroM M)(zeroM M)(zeroM M)
    (code_numeral M 1)sb sc shifted PCondition HShift HS) as PShifted.
  destruct(environment_cons_total M sb sc pn guard) as(ub&uc&un&HConsG).
  assert(HBranch:context_bounded M ub uc un(succM M k)).
  { exact(proj2(context_bounded_cons M sb sc pn guard ub uc un(succM M k)HConsG)(conj HG HShiftB)). }
  assert(PConclusion:source_full_prv M ub uc un conclusion).
  { exact(source_full_modus_ponens M ub uc un shifted conclusion pointImp HPI
      (source_full_prv_weaken_bounded M sb sc pn ub uc un pointImp(succM M k)PPointImp
        (source_cons_tail_inclusion M sb sc pn guard ub uc un HConsG)HBranch)
      (source_full_prv_weaken_bounded M sb sc pn ub uc un shifted(succM M k)PShifted
        (source_cons_tail_inclusion M sb sc pn guard ub uc un HConsG)HBranch)). }
  pose proof(full_source_II M sb sc pn guard conclusion point ub uc un
    (ex_intro _ (succM M k)(conj HPointB HShiftB))PConclusion HConsG HP) as PPoint.
  pose proof(full_source_AllI M pb pc pn point all sb sc(ex_intro _ k(conj HAllB HPCtx))PPoint HShift HA) as PAll.
  exists b,c,n. split;[exact HCtx|].
  apply(full_source_II M b c n condition all result pb pc pn);try assumption.
  exists k. split;[|exact HCtxB].
  exact(proj2(source_bounded_accept_binary M SFImpl condition all result k
    (or_intror(or_intror eq_refl))HR)(conj HB HAllB)).
Qed.

Print Assumptions source_zfr_cb_all_intro.
