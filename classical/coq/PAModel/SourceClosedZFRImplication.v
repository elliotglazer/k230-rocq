(** A generated closed ZFR context can be collected outside an ordinary
    hypothesis branch before fresh existential elimination. The opened
    hypothesis may use names arbitrarily far above the original bound. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension CodeExpressions SetFormulaCodes
 SourceBounded SourceBoundMonotone SourceTraceBounds NumericalContexts NumericalEnvironments NumericalSourceFull
 ContextCombination SourceContextTransport SourceClosedContextShift SourceProofWeakening
 SourceLeastOrdinalWitness SourceUpperProofHelpers SourceZFRProvability.
Unset Implicit Arguments.
Theorem source_full_closed_zfr_implication M b c n opened goal bb bc bn ab ac an ub uc un imp k:
 context_bounded M b c n k ->environment_cons M b c n opened bb bc bn ->
 source_zfr_context M ab ac an ->context_union M bb bc bn ab ac an ub uc un ->
 source_full_prv M ub uc un goal ->sf_relation M SFImpl opened goal imp ->
 exists vb vc vn,context_union M b c n ab ac an vb vc vn /\context_bounded M vb vc vn k /\
 source_full_prv M vb vc vn imp.
Proof.
 intros BC HCons HZFR HU PGoal HImp.
 pose proof(source_zfr_context_closed M ab ac an HZFR)as BClosed.
 pose proof(context_bounded_monotone M ab ac an(zeroM M)k BClosed(coding_zero_lt_succ M k))as BN.
 destruct(context_union_total M b c n ab ac an)as(vb&vc&vn&HV).
 pose proof(source_context_union_bounded M b c n ab ac an vb vc vn k HV BC BN)as BV.
 pose proof(context_union_left M b c n ab ac an vb vc vn HV)as HVLeft.
 pose proof(context_union_right M b c n ab ac an vb vc vn HV)as HVRight.
 destruct(source_full_prv_wellformed M ub uc un goal PGoal)as(q&BGoalQ&BU).
 assert(BOpened:source_bounded M opened q).
 { apply BU. apply(context_union_left M bb bc bn ab ac an ub uc un HU).
   apply(proj2(context_member_cons M b c n opened bb bc bn opened HCons)). now left. }
 set(K:=addM M k q).
 assert(BVK:context_bounded M vb vc vn K).
 { exact(context_bounded_monotone M vb vc vn k K BV(coding_le_add M k q)). }
 assert(BOpenedK:source_bounded M opened K).
 { apply(source_bounded_monotone M opened q K BOpened). unfold K. rewrite Arithmetic.add_comm. apply coding_le_add. }
 destruct(environment_cons_total M vb vc vn opened)as(wb&wc&wn&HW).
 pose proof(proj2(context_bounded_cons M vb vc vn opened wb wc wn K HW)(conj BOpenedK BVK))as BW.
 pose proof(source_context_included_cons M b c n vb vc vn opened bb bc bn wb wc wn HVLeft HCons HW)as HBranch.
 assert(HN:context_included M ab ac an wb wc wn).
 { intros f HF. exact(source_cons_tail_inclusion M vb vc vn opened wb wc wn HW f(HVRight f HF)). }
 assert(HIncluded:context_included M ub uc un wb wc wn).
 { intros f HF. apply(proj2 HU f)in HF. destruct HF as[HF|HF];[exact(HBranch f HF)|exact(HN f HF)]. }
 pose proof(source_full_prv_weaken_bounded M ub uc un wb wc wn goal K PGoal HIncluded BW)as PGoalW.
 exists vb,vc,vn. split;[exact HV|]. split;[exact BV|].
 exact(source_full_implication_intro M vb vc vn opened goal imp wb wc wn HW HImp PGoalW).
Qed.
Print Assumptions source_full_closed_zfr_implication.
