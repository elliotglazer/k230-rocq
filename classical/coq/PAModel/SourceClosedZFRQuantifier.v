(** Pull an actually generated closed ZFR context out of a guarded
    quantifier branch, preserving the original arbitrary source context. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourceTraceBounds
 NumericalContexts NumericalEnvironments NumericalContextRenaming NumericalSourceFull ContextCombination
 SourceContextTransport SourceClosedContextShift SourceProofWeakening SourceLeastOrdinalWitness SourceZFRProvability.
Unset Implicit Arguments.

Theorem source_full_closed_zfr_guarded_all M b c n sb sc guard bb bc bn ab ac an ub uc un request point whole k:
 context_bounded M b c n k ->source_bounded M whole k ->context_shift M b c n sb sc ->
 environment_cons M sb sc n guard bb bc bn ->source_zfr_context M ab ac an ->
 context_union M bb bc bn ab ac an ub uc un ->sf_relation M SFImpl guard request point ->
 sf_relation M SFAll point(zeroM M)whole ->source_full_prv M ub uc un request ->
 exists vb vc vn,context_union M b c n ab ac an vb vc vn /\source_full_prv M vb vc vn whole.
Proof.
 intros BC BW HS HCons HZFR HU HPoint HAll PRequest.
 pose proof(source_zfr_context_closed M ab ac an HZFR)as BClosed.
 pose proof(context_bounded_monotone M ab ac an(zeroM M)k BClosed(coding_zero_lt_succ M k))as BN.
 destruct(context_union_total M b c n ab ac an)as(vb&vc&vn&HV).
 pose proof(source_context_union_bounded M b c n ab ac an vb vc vn k HV BC BN)as BV.
 pose proof(context_union_left M b c n ab ac an vb vc vn HV)as HVLeft.
 pose proof(context_union_right M b c n ab ac an vb vc vn HV)as HVRight.
 destruct(context_shift_total M vb vc vn)as(vs&vt&HVS).
 pose proof(context_shift_preserves_bound M vb vc vn vs vt k HVS BV)as BVS.
 pose proof(source_context_included_shift M b c n vb vc vn sb sc vs vt HVLeft HS HVS)as HShiftLeft.
 pose proof(proj1(source_bounded_accept_unary M SFAll point whole k(or_introl eq_refl)HAll)BW)as BP.
 pose proof(proj1(proj1(source_bounded_accept_binary M SFImpl guard request point(succM M k)
  (or_intror(or_intror eq_refl))HPoint)BP))as BG.
 destruct(environment_cons_total M vs vt vn guard)as(nb&nc&nn&HN).
 pose proof(proj2(context_bounded_cons M vs vt vn guard nb nc nn(succM M k)HN)(conj BG BVS))as BNew.
 pose proof(source_context_included_cons M sb sc n vs vt vn guard bb bc bn nb nc nn HShiftLeft HCons HN)as HBranch.
 pose proof(source_context_included_shift M ab ac an vb vc vn ab ac vs vt HVRight
  (source_closed_context_shift_self M ab ac an BClosed)HVS)as HClosedShift.
 assert(HClosedNew:context_included M ab ac an nb nc nn).
 { intros f HF. exact(source_cons_tail_inclusion M vs vt vn guard nb nc nn HN f(HClosedShift f HF)). }
 assert(HIncluded:context_included M ub uc un nb nc nn).
 { intros f HF. apply(proj2 HU f)in HF. destruct HF as[HF|HF];[exact(HBranch f HF)|exact(HClosedNew f HF)]. }
 pose proof(source_full_prv_weaken_bounded M ub uc un nb nc nn request(succM M k)PRequest HIncluded BNew)as PRequestNew.
 pose proof(full_source_II M vs vt vn guard request point nb nc nn
  (ex_intro _(succM M k)(conj BP BVS))PRequestNew HN HPoint)as PPoint.
 exists vb,vc,vn. split;[exact HV|].
 exact(full_source_AllI M vb vc vn point whole vs vt(ex_intro _ k(conj BW BV))PPoint HVS HAll).
Qed.
Print Assumptions source_full_closed_zfr_guarded_all.
