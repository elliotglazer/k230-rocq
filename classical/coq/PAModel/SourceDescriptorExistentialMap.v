(** Actual descriptor existential congruence. The premise is a source
    proof of the point implication, not an assumed proof transformer. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 NumericalContexts NumericalEnvironments NumericalContextRenaming SourceClosedContextShift
 SourceDescriptorProvability SourceDescriptorClosure SourceContextProofHelpers SourceContextTransport SourceNamedProofRules
 SourceClosedShift NumericalRenaming SourceProofWeakening SourceTraceBounds
 SourceImplicationAllShift SourceSequents NumericalSourceFull.
Unset Implicit Arguments.

Theorem source_descriptor_exists_map M T f g exf exg point result k :
 source_bounded M f(succM M k) ->source_bounded M g(succM M k) ->
 sf_relation M SFEx f(zeroM M) exf ->sf_relation M SFEx g(zeroM M) exg ->
 sf_relation M SFImpl f g point ->sf_relation M SFImpl exf exg result ->
 source_descriptor_provable M T point ->source_descriptor_provable M T result.
Proof.
 intros HF HG HEF HEG HPoint HResult(b&c&n&HCtx&PP).
 pose proof(proj2(source_bounded_accept_unary M SFEx f exf k(or_intror eq_refl) HEF) HF)as BExF.
 pose proof(proj2(source_bounded_accept_unary M SFEx g exg k(or_intror eq_refl) HEG) HG)as BExG.
 assert(BResult:source_bounded M result k).
 { exact(proj2(source_bounded_accept_binary M SFImpl exf exg result k
   (or_intror(or_intror eq_refl)) HResult)(conj BExF BExG)). }
 assert(C0:context_bounded M b c n k).
 { exact(context_bounded_monotone M b c n(zeroM M) k(proj1 HCtx)(coding_zero_lt_succ M k)). }
 destruct(environment_cons_total M b c n exf)as(b1&c1&n1&H1).
 assert(C1:context_bounded M b1 c1 n1 k).
 { exact(proj2(context_bounded_cons M b c n exf b1 c1 n1 k H1)(conj BExF C0)). }
 destruct(context_shift_total M b1 c1 n1)as(sb&sc&HShift).
 assert(C2:context_bounded M sb sc n1(succM M k)).
 { exact(context_shift_preserves_bound M b1 c1 n1 sb sc k HShift C1). }
 pose proof(source_full_cons_head M b c n exf b1 c1 n1 k H1 BExF C1)as PExF.
 assert(Included:context_included M b c n sb sc n1).
 { intros ax HAx.
   assert(HIn1:context_member M b1 c1 n1 ax).
   { apply(proj2(context_member_cons M b c n exf b1 c1 n1 ax H1)). now right. }
   destruct(context_renaming_member_forward M b1 c1 n1(zeroM M)(zeroM M)(zeroM M)
    (code_numeral M 1) sb sc ax HShift HIn1)as(shifted&HIn&HR).
   pose proof(source_closed_shift_self M ax(proj1 HCtx ax HAx))as HSelf.
   rewrite(numerical_renaming_functional M ax _ _ _ _ shifted ax HR HSelf)in HIn. exact HIn. }
 assert(PPoint:source_full_prv M sb sc n1 point).
 { exact(source_full_prv_weaken_bounded M b c n sb sc n1 point(succM M k) PP Included C2). }
 pose proof(source_full_existential_map_shift M b1 c1 n1 f g exf exg point sb sc
   HEF HEG HPoint HShift PExF PPoint)as PExG.
 exists b,c,n. split;[exact HCtx|].
 exact(full_source_II M b c n exf exg result b1 c1 n1(ex_intro _ k(conj BResult C0)) PExG H1 HResult).
Qed.
Print Assumptions source_descriptor_exists_map.
