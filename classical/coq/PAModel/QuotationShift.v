(** Source de Bruijn shift commutes with quotation when an environment entry
    is prepended. The quotation fresh/domain parameters stay exactly equal.
    The prepended value need not equal the fresh parameter. No alpha-conversion
    or automatic hygiene theorem is asserted. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
  NumericalEnvironments NumericalContexts NumericalContextRenaming NumericalContextQuotation
  NumericalRenaming NumericalSubstitutionMaps NumericalSubstitution RenamingSubstitution
  SourceBounded SubstitutionEnvironment QuotationSubstitution
  NumericalQuotation QuotationFunctionality.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Lemma quotation_substitution_shift_lookup M i x :
  substitution_lookup M (zeroM M) (zeroM M) (zeroM M) (succM M (zeroM M)) i x <->
  x=succM M i.
Proof.
  pose proof (renaming_substitution_lookup M (zeroM M) (zeroM M) (zeroM M)
    (succM M (zeroM M)) i x) as H.
  rewrite Arithmetic.add_zero in H. rewrite <- H. apply context_shift_lookup.
Qed.

Theorem quotation_shift_cons_agreement M b c n inserted b' c' n' bound :
  environment_cons M b c n inserted b' c' n' ->
  substitution_environment_agreement M (zeroM M) (zeroM M) (zeroM M)
    (succM M (zeroM M)) b' c' n' b c n bound.
Proof.
  intros Hcons i x y z Hi Hix Hxy Hiz.
  apply quotation_substitution_shift_lookup in Hix. subst x.
  apply (proj1 (environment_cons_tail M b c n inserted b' c' n' i y Hcons)) in Hxy.
  exact (environment_lookup_functional M b c n i y z Hxy Hiz).
Qed.

Theorem quotation_shift_cons M f g bound b c n inserted b' c' n' newFresh domain v w :
  source_bounded M f bound ->
  numerical_renaming M f (zeroM M) (zeroM M) (zeroM M) (succM M (zeroM M)) g ->
  environment_cons M b c n inserted b' c' n' ->
  numerical_quotation M f b c n newFresh domain v ->
  numerical_quotation M g b' c' n' newFresh domain w -> v=w.
Proof.
  intros Hbound Hshift Hcons Hv Hw.
  apply (numerical_quotation_substitution M f bound
    (zeroM M) (zeroM M) (zeroM M) (succM M (zeroM M))
    b' c' n' b c n newFresh domain g v w Hbound).
  - exact (quotation_shift_cons_agreement M b c n inserted b' c' n' bound Hcons).
  - apply (proj1 (numerical_renaming_empty_substitution M f (zeroM M) (zeroM M)
      (succM M (zeroM M)) g)). exact Hshift.
  - exact Hv.
  - exact Hw.
Qed.

Corollary quotation_shift_cons_iff M f g bound b c n inserted b' c' n' newFresh domain v :
  source_bounded M f bound ->
  numerical_renaming M f (zeroM M) (zeroM M) (zeroM M) (succM M (zeroM M)) g ->
  environment_cons M b c n inserted b' c' n' ->
  (numerical_quotation M f b c n newFresh domain v <->
   numerical_quotation M g b' c' n' newFresh domain v).
Proof.
  intros Hbound Hshift Hcons. split.
  - intro Hv. destruct (numerical_quotation_total M g b' c' n' newFresh domain) as [w Hw].
    assert (v=w) by exact (quotation_shift_cons M f g bound b c n inserted b' c' n'
      newFresh domain v w Hbound Hshift Hcons Hv Hw).
    now subst w.
  - intro Hv. destruct (numerical_quotation_total M f b c n newFresh domain) as [w Hw].
    assert (w=v) by exact (quotation_shift_cons M f g bound b c n inserted b' c' n'
      newFresh domain w v Hbound Hshift Hcons Hw Hv).
    now subst w.
Qed.

Theorem context_quotation_shift_cons M sb sc len shiftedB shiftedC bound
    eb ec en inserted eb' ec' en' newFresh domain tb tc :
  context_shift M sb sc len shiftedB shiftedC ->
  context_bounded M sb sc len bound ->
  environment_cons M eb ec en inserted eb' ec' en' ->
  (context_quotation M sb sc len eb ec en newFresh domain tb tc <->
   context_quotation M shiftedB shiftedC len eb' ec' en' newFresh domain tb tc).
Proof.
  intros Hshift Hbound Hcons. split.
  - intros Hctx i g q Hi Hg Hq.
    destruct (beta_total M sb sc i) as [f Hf].
    pose proof (Hshift i f g Hi Hf Hg) as Hfg.
    assert (Hb : source_bounded M f bound) by (apply Hbound; exists i; auto).
    apply (proj1 (quotation_shift_cons_iff M f g bound eb ec en inserted eb' ec' en'
      newFresh domain q Hb Hfg Hcons)). exact (Hctx i f q Hi Hf Hq).
  - intros Hctx i f q Hi Hf Hq.
    destruct (beta_total M shiftedB shiftedC i) as [g Hg].
    pose proof (Hshift i f g Hi Hf Hg) as Hfg.
    assert (Hb : source_bounded M f bound) by (apply Hbound; exists i; auto).
    apply (proj2 (quotation_shift_cons_iff M f g bound eb ec en inserted eb' ec' en'
      newFresh domain q Hb Hfg Hcons)). exact (Hctx i g q Hi Hg Hq).
Qed.

Corollary context_quotation_shift_cons_total M sb sc len shiftedB shiftedC bound
    eb ec en inserted eb' ec' en' newFresh domain :
  context_shift M sb sc len shiftedB shiftedC ->
  context_bounded M sb sc len bound ->
  environment_cons M eb ec en inserted eb' ec' en' ->
  exists tb tc, context_quotation M sb sc len eb ec en newFresh domain tb tc /\
    context_quotation M shiftedB shiftedC len eb' ec' en' newFresh domain tb tc.
Proof.
  intros Hshift Hbound Hcons.
  destruct (context_quotation_total M sb sc len eb ec en newFresh domain) as [tb [tc Hctx]].
  exists tb,tc. split; [exact Hctx|].
  apply (proj1 (context_quotation_shift_cons M sb sc len shiftedB shiftedC bound
    eb ec en inserted eb' ec' en' newFresh domain tb tc Hshift Hbound Hcons)). exact Hctx.
Qed.

Print Assumptions quotation_substitution_shift_lookup.
Print Assumptions quotation_shift_cons_agreement.
Print Assumptions quotation_shift_cons.
Print Assumptions quotation_shift_cons_iff.
Print Assumptions context_quotation_shift_cons.
Print Assumptions context_quotation_shift_cons_total.
