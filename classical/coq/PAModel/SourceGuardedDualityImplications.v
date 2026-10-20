(** Actual empty-context implications for guarded duality. No theorem
    about a matrix is assumed, and the context rules operate on real codes. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded NumericalContexts NumericalEnvironments NumericalSourceFull
 SourceContextProofHelpers SourceGuardedQuantifierDuality SourceDescriptorProvability SourceDescriptorClosure.
Unset Implicit Arguments.
Theorem source_guarded_duality_empty M guard a implication negA both exBoth notBoth all forward reverse k:
 source_bounded M guard(succM M k)->source_bounded M a(succM M k)->
 sf_relation M SFImpl guard a implication->sf_relation M SFImpl a(zeroM M)negA->
 sf_relation M SFAnd guard negA both->sf_relation M SFEx both(zeroM M)exBoth->
 sf_relation M SFImpl exBoth(zeroM M)notBoth->sf_relation M SFAll implication(zeroM M)all->
 sf_relation M SFImpl notBoth all forward->sf_relation M SFImpl all notBoth reverse->
 source_full_prv M(zeroM M)(zeroM M)(zeroM M)forward/\source_full_prv M(zeroM M)(zeroM M)(zeroM M)reverse.
Proof.
 intros BG BA HI HNA HB HE HN HAll HF HR.
 assert(BI:source_bounded M implication(succM M k)).
 { exact(proj2(source_bounded_accept_binary M SFImpl guard a implication _(or_intror(or_intror eq_refl))HI)(conj BG BA)). }
 assert(BNA:source_bounded M negA(succM M k)).
 { exact(proj2(source_bounded_accept_binary M SFImpl a(zeroM M)negA _(or_intror(or_intror eq_refl))HNA)(conj BA(source_bounded_accept_falsity M _))). }
 assert(BBoth:source_bounded M both(succM M k)).
 { exact(proj2(source_bounded_accept_binary M SFAnd guard negA both _(or_introl eq_refl)HB)(conj BG BNA)). }
 pose proof(proj2(source_bounded_accept_unary M SFEx both exBoth k(or_intror eq_refl)HE)BBoth)as BE.
 assert(BN:source_bounded M notBoth k).
 { exact(proj2(source_bounded_accept_binary M SFImpl exBoth(zeroM M)notBoth k(or_intror(or_intror eq_refl))HN)(conj BE(source_bounded_accept_falsity M _))). }
 pose proof(proj2(source_bounded_accept_unary M SFAll implication all k(or_introl eq_refl)HAll)BI)as BAll.
 assert(BF:source_bounded M forward k).
 { exact(proj2(source_bounded_accept_binary M SFImpl notBoth all forward k(or_intror(or_intror eq_refl))HF)(conj BN BAll)). }
 assert(BR:source_bounded M reverse k).
 { exact(proj2(source_bounded_accept_binary M SFImpl all notBoth reverse k(or_intror(or_intror eq_refl))HR)(conj BAll BN)). }
 split.
 - destruct(environment_cons_total M(zeroM M)(zeroM M)(zeroM M)notBoth)as(b&c&n&HC).
   assert(BC:context_bounded M b c n k).
   { apply(proj2(context_bounded_cons M _ _ _ notBoth b c n k HC)). exact(conj BN(context_bounded_empty M _ _ k)). }
   pose proof(source_full_cons_head M _ _ _ notBoth b c n k HC BN BC)as PN.
   pose proof(source_full_guarded_all_from_not_exists_neg M b c n guard a implication negA both exBoth notBoth all k BC BG BA HI HNA HB HE HN HAll PN)as PA.
   exact(full_source_II M _ _ _ notBoth all forward b c n(ex_intro _ k(conj BF(context_bounded_empty M _ _ k)))PA HC HF).
 - destruct(environment_cons_total M(zeroM M)(zeroM M)(zeroM M)all)as(b&c&n&HC).
   assert(BC:context_bounded M b c n k).
   { apply(proj2(context_bounded_cons M _ _ _ all b c n k HC)). exact(conj BAll(context_bounded_empty M _ _ k)). }
   pose proof(source_full_cons_head M _ _ _ all b c n k HC BAll BC)as PA.
   pose proof(source_full_not_exists_neg_from_guarded_all M b c n guard a implication negA both exBoth notBoth all k BC BG BA HI HNA HB HE HN HAll PA)as PN.
   exact(full_source_II M _ _ _ all notBoth reverse b c n(ex_intro _ k(conj BR(context_bounded_empty M _ _ k)))PN HC HR).
Qed.
Print Assumptions source_guarded_duality_empty.
