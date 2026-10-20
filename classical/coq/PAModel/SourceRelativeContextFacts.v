(** Addition of a source assumption and monotonicity of the combined
    relativized/domain context, including arbitrary internal domain bounds. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT
  NumericalContexts NumericalEnvironments ContextCombination
  SourceRelativization SourceRelativizedContexts SourceRelativeContexts.
Unset Implicit Arguments.

Lemma context_union_cons_left M b c n d e m u v l h b' c' n' u' v' l' :
  context_union M b c n d e m u v l ->
  environment_cons M b c n h b' c' n' ->
  environment_cons M u v l h u' v' l' ->
  context_union M b' c' n' d e m u' v' l'.
Proof.
  intros [EL HU] HB HUV. split.
  - rewrite (proj1 HB),(proj1 HUV),EL,Arithmetic.add_succ. reflexivity.
  - intro f. rewrite (context_member_cons M u v l h u' v' l' f HUV).
    rewrite (context_member_cons M b c n h b' c' n' f HB),HU. tauto.
Qed.

Theorem source_relative_context_cons M domain b c n k u v l f g b' c' n' u' v' l' :
  source_relative_context M domain b c n k u v l ->
  source_relativization M domain f g ->
  environment_cons M b c n f b' c' n' ->
  environment_cons M u v l g u' v' l' ->
  source_relative_context M domain b' c' n' k u' v' l'.
Proof.
  intros [mb [mc [db [dc [HM [HD HU]]]]]] HFG HSource HTarget.
  destruct (environment_cons_total M mb mc n g) as [mb' [mc' [n'' HMCons]]].
  assert (EN:n''=n') by (rewrite (proj1 HSource);exact (proj1 HMCons)). subst n''.
  exists mb',mc',db,dc. split.
  - exact (source_context_relativization_cons M domain b c n mb mc f g b' c' n' mb' mc' HM HFG HSource HMCons).
  - split;[exact HD|]. exact (context_union_cons_left M mb mc n db dc k u v l g
      mb' mc' n' u' v' l' HU HMCons HTarget).
Qed.

Theorem source_relative_context_included M domain b c n k u v l b' c' n' k' u' v' l' :
  source_relative_context M domain b c n k u v l ->
  source_relative_context M domain b' c' n' k' u' v' l' ->
  context_included M b c n b' c' n' ->
  (forall i,coding_lt M i k -> coding_lt M i k') ->
  context_included M u v l u' v' l'.
Proof.
  intros HR HR' HInc HBound f HF.
  apply (proj2 (source_relative_context_member_iff M domain b' c' n' k' u' v' l' f HR')).
  apply (proj1 (source_relative_context_member_iff M domain b c n k u v l f HR)) in HF.
  destruct HF as [[g [HG HRel]]|[i [HI HInst]]].
  - left. exists g. split;[exact (HInc g HG)|exact HRel].
  - right. exists i. split;[exact (HBound i HI)|exact HInst].
Qed.

Theorem source_relative_context_monotone M domain b c n k u v l k' u' v' l' :
  source_relative_context M domain b c n k u v l ->
  source_relative_context M domain b c n k' u' v' l' ->
  coding_lt M k (succM M k') -> context_included M u v l u' v' l'.
Proof.
  intros HR HR' HKK. apply (source_relative_context_included M domain b c n k u v l
    b c n k' u' v' l' HR HR' (context_included_refl M b c n)).
  intros i HI. destruct (proj1 (coding_lt_succ_cases M k k') HKK) as [Hlt|E].
  - exact (coding_lt_trans M i k k' HI Hlt).
  - now rewrite <- E.
Qed.

Theorem source_relative_context_representation_included M domain b c n k u v l u' v' l' :
  source_relative_context M domain b c n k u v l ->
  source_relative_context M domain b c n k u' v' l' ->
  context_included M u v l u' v' l'.
Proof.
  intros HR HR'. apply (source_relative_context_included M domain b c n k u v l
    b c n k u' v' l' HR HR' (context_included_refl M b c n)). auto.
Qed.

Print Assumptions source_relative_context_cons.
Print Assumptions source_relative_context_included.
Print Assumptions source_relative_context_monotone.
Print Assumptions source_relative_context_representation_included.
