(** Genuine source proofs extracting the first parameter and tail block.
    All lengths and role names may be nonstandard PA-model values. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 SourceMembershipBlocks SourceMembershipBlockProofs SourceQuantifierRules SourceSequents NumericalContexts
 NumericalEnvironments NumericalSourceFull SourceContextProofHelpers.
Unset Implicit Arguments.
Lemma source_block_tail_index M i start:addM M i(succM M start)=addM M(succM M i)start.
Proof. rewrite(Arithmetic.add_comm M i(succM M start)),!Arithmetic.add_succ,(Arithmetic.add_comm M start i). reflexivity. Qed.
Theorem source_full_membership_block_head_tail M start y count whole tail head b c n k:
 (forall i,coding_lt M i(succM M count)->coding_lt M(addM M i start)k)->coding_lt M y k->
 source_membership_block M start y(succM M count)whole->source_membership_block M(succM M start)y count tail->
 sf_relation M SFMember start y head->context_bounded M b c n k->source_full_prv M b c n whole->
 source_full_prv M b c n head /\source_full_prv M b c n tail.
Proof.
 intros HNames HY HWhole HTail HHead HC PWhole. split.
 - apply(source_full_membership_block_project M start y(succM M count)whole b c n k(zeroM M)head HNames HY HWhole HC PWhole
    (coding_zero_lt_succ M count)). now rewrite Arithmetic.add_zero.
 - apply(source_full_membership_block_intro M(succM M start)y count tail b c n k).
   + intros i HI. rewrite source_block_tail_index. apply HNames,coding_lt_succ_cancel. exact HI.
   + exact HY.
   + exact HTail.
   + exact HC.
   + intros i f HI HF. rewrite source_block_tail_index in HF.
     exact(source_full_membership_block_project M start y(succM M count)whole b c n k(succM M i)f
      HNames HY HWhole HC PWhole(proj2(coding_lt_succ_cancel M i count)HI)HF).
Qed.
Theorem source_membership_block_head_tail_laws M start y count whole tail head headlaw taillaw k:
 (forall i,coding_lt M i(succM M count)->coding_lt M(addM M i start)k)->coding_lt M y k->
 source_membership_block M start y(succM M count)whole->source_membership_block M(succM M start)y count tail->
 sf_relation M SFMember start y head->sf_relation M SFImpl whole head headlaw->sf_relation M SFImpl whole tail taillaw->
 source_full_prv M(zeroM M)(zeroM M)(zeroM M)headlaw /\
 source_full_prv M(zeroM M)(zeroM M)(zeroM M)taillaw.
Proof.
 intros HNames HY HWhole HTail HHead HHeadLaw HTailLaw.
 assert(BWhole:source_bounded M whole k)by(exact(source_membership_block_bound M start y(succM M count)whole k HNames HY HWhole)).
 assert(BHead:source_bounded M head k).
 { apply(proj2(source_bounded_accept_atom M SFMember start y head k(or_introl eq_refl)HHead)).
   split;[|exact HY]. pose proof(HNames(zeroM M)(coding_zero_lt_succ M count))as H. now rewrite Arithmetic.add_zero in H. }
 assert(BTail:source_bounded M tail k).
 { apply(source_membership_block_bound M(succM M start)y count tail k);try assumption.
   intros i HI. rewrite source_block_tail_index. apply HNames,coding_lt_succ_cancel. exact HI. }
 destruct(environment_cons_total M(zeroM M)(zeroM M)(zeroM M)whole)as(b&c&n&HCons).
 assert(HCtx:context_bounded M b c n k).
 { apply(proj2(context_bounded_cons M _ _ _ whole b c n k HCons)). split;[exact BWhole|apply context_bounded_empty]. }
 pose proof(source_full_cons_head M _ _ _ whole b c n k HCons BWhole HCtx)as PWhole.
 destruct(source_full_membership_block_head_tail M start y count whole tail head b c n k HNames HY HWhole HTail HHead HCtx PWhole)
 as(PHead&PTail). split.
 - apply(full_source_II M(zeroM M)(zeroM M)(zeroM M)whole head headlaw b c n);try assumption.
   exists k. split;[|apply context_bounded_empty].
   exact(proj2(source_bounded_accept_binary M SFImpl whole head headlaw k(or_intror(or_intror eq_refl))HHeadLaw)(conj BWhole BHead)).
 - apply(full_source_II M(zeroM M)(zeroM M)(zeroM M)whole tail taillaw b c n);try assumption.
   exists k. split;[|apply context_bounded_empty].
   exact(proj2(source_bounded_accept_binary M SFImpl whole tail taillaw k(or_intror(or_intror eq_refl))HTailLaw)(conj BWhole BTail)).
Qed.
Print Assumptions source_full_membership_block_head_tail.
Print Assumptions source_membership_block_head_tail_laws.
