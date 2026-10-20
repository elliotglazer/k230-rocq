(** Replace internally many source hypotheses by actual proofs in a fixed
    target context. PA induction on context length suffices: move the last
    hypothesis to the head, use implication introduction, and apply MP. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  NumericalProofs NumericalContexts NumericalEnvironments SourceContextTransport
  SourceBounded SourceSequents SetFormulaCodes SetCodeDescent NumericalSourceFull
  SourceProofWeakening.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_hypothesis_transport_at M u v l n :=
  forall b c f,source_full_prv M b c n f ->
    (forall h,context_member M b c n h -> source_full_prv M u v l h) ->
    source_full_prv M u v l f.

Definition source_hypothesis_transport_formula : form :=
  ∀∀∀ (source_full_prv_formula $2 $1 $3 $0 →
    (∀ (context_member_formula $3 $2 $4 $0 → source_full_prv_formula $5 $6 $7 $0)) →
    source_full_prv_formula $4 $5 $6 $0).
Local Opaque holds source_full_prv_formula context_member_formula.

Lemma source_hypothesis_transport_definable M u v l :
  Definable1 M (source_hypothesis_transport_at M u v l).
Proof.
  exists source_hypothesis_transport_formula,(u .: v .: l .: fun _=>zeroM M). intro n.
  unfold source_hypothesis_transport_at,source_hypothesis_transport_formula.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite source_full_prv_formula_correct.
  setoid_rewrite context_member_formula_correct. reflexivity.
Qed.

Theorem source_full_prv_replace_hypotheses M u v l :
  source_context_finite_bound M u v l ->
  forall n b c f,source_full_prv M b c n f ->
    (forall h,context_member M b c n h -> source_full_prv M u v l h) ->
    source_full_prv M u v l f.
Proof.
  intros HTarget.
  apply (definable_induction M (source_hypothesis_transport_at M u v l)
    (source_hypothesis_transport_definable M u v l)).
  - intros b c f HP HH.
    apply (source_full_prv_weaken M b c (zeroM M) u v l f HP);[|exact HTarget].
    intros h HM. exfalso. exact (context_empty M b c h HM).
  - intros n IH b c f HP HH.
    destruct (source_full_prv_wellformed M b c (succM M n) f HP) as [k [HF HC]].
    destruct (beta_total M b c n) as [h HLast].
    assert (HMember:context_member M b c (succM M n) h).
    { exists n. split;[apply coding_lt_succ|exact HLast]. }
    assert (HPrefix:context_bounded M b c n k).
    { intros a [i [HI HA]]. apply HC. exists i. split;[|exact HA].
      exact (coding_lt_trans M i n (succM M n) HI (coding_lt_succ M n)). }
    destruct (environment_cons_total M b c n h) as [sb [sc [sn HCons]]].
    assert (EN:sn=succM M n) by exact (proj1 HCons). subst sn.
    assert (HTail:context_bounded M sb sc (succM M n) k).
    { apply (proj2 (context_bounded_cons M b c n h sb sc (succM M n) k HCons)).
      split;[exact (HC h HMember)|exact HPrefix]. }
    assert (PHead:source_full_prv M sb sc (succM M n) f).
    { apply (source_full_prv_weaken_bounded M b c (succM M n) sb sc (succM M n) f k HP);[|exact HTail].
      intros a [i [HI HA]].
      apply (proj2 (context_member_cons M b c n h sb sc (succM M n) a HCons)).
      destruct (proj1 (coding_lt_succ_cases M i n) HI) as [Hin|E].
      - right. exists i. auto.
      - left. subst i. exact (beta_unique M b c n a h HA HLast). }
    destruct (sf_relation_total M SFImpl h f) as [imp HImp].
    assert (PImp:source_full_prv M b c n imp).
    { apply (full_source_II M b c n h f imp sb sc (succM M n));[|exact PHead|exact HCons|exact HImp].
      exists k. split;[|exact HPrefix].
      apply (proj2 (source_bounded_accept_binary M SFImpl h f imp k
        (or_intror (or_intror eq_refl)) HImp)). split;[exact (HC h HMember)|exact HF]. }
    assert (PTImp:source_full_prv M u v l imp).
    { apply (IH b c imp PImp). intros a [i [HI HA]]. apply HH. exists i.
      split;[exact (coding_lt_trans M i n (succM M n) HI (coding_lt_succ M n))|exact HA]. }
    destruct (source_full_prv_wellformed M u v l imp PTImp) as [kt [HIF HTC]].
    apply (full_source_IE M u v l h f imp);[|exact PTImp|exact (HH h HMember)|exact HImp].
    exists kt. split;[|exact HTC].
    exact (proj2 (proj1 (source_bounded_accept_binary M SFImpl h f imp kt
      (or_intror (or_intror eq_refl)) HImp) HIF)).
Qed.

Print Assumptions source_hypothesis_transport_definable.
Print Assumptions source_full_prv_replace_hypotheses.
