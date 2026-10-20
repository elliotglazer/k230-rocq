(** Pull a generated closed ZFR context out of a genuine fresh-witness
    branch. Freshness is relative to the original context and conclusion;
    no bound on the new witness name is imposed on the branch proof. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension CodeExpressions SetFormulaCodes SourceBounded
 SourceBoundMonotone SourceTraceBounds NumericalContexts NumericalEnvironments NumericalSourceFull
 NumericalInstantiation ContextCombination SourceContextTransport SourceClosedContextShift SourceProofWeakening
 SourceLeastOrdinalWitness SourceUpperProofHelpers SourceFreshQuantifierProofs SourceZFRProvability.
Unset Implicit Arguments.
Theorem source_full_closed_zfr_fresh_exists M b c n body ex x opened goal bb bc bn ab ac an ub uc un k:
 context_bounded M b c n k ->source_bounded M goal k ->source_bounded M body(succM M k) ->
 coding_lt M k(succM M x) ->sf_relation M SFEx body(zeroM M)ex ->
 numerical_instantiation M body x opened ->environment_cons M b c n opened bb bc bn ->
 source_zfr_context M ab ac an ->context_union M bb bc bn ab ac an ub uc un ->
 source_full_prv M ub uc un goal ->source_full_prv M b c n ex ->
 exists vb vc vn,context_union M b c n ab ac an vb vc vn /\source_full_prv M vb vc vn goal.
Proof.
 intros BC BG BBody HX HEx HInst HCons HZFR HU PGoal PEx.
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
 destruct(sf_relation_total M SFImpl opened goal)as(imp&HImp).
 pose proof(source_full_implication_intro M vb vc vn opened goal imp wb wc wn HW HImp PGoalW)as PImp.
 pose proof(source_full_prv_weaken_bounded M b c n vb vc vn ex k PEx HVLeft BV)as PExV.
 exists vb,vc,vn. split;[exact HV|].
 exact(source_full_fresh_exists_elim M vb vc vn body ex x opened goal imp k
  BV BBody BG HX HEx HInst HImp PImp PExV).
Qed.
Print Assumptions source_full_closed_zfr_fresh_exists.
