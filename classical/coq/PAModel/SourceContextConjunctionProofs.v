(** Actual numerical source proofs introduce and project an internally
    finite conjunction, using PA-definable induction on its coded length. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes
  SourceBounded NumericalProofs NumericalContexts NumericalEnvironments NumericalSourceFull
  SourceContextConjunction.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_context_conjunction_intro_at M n :=forall sb sc result b c l k,
  source_context_conjunction M sb sc n result ->context_bounded M sb sc n k ->
  context_bounded M b c l k ->
  (forall h,context_member M sb sc n h ->source_full_prv M b c l h) ->
  source_bounded M result k /\source_full_prv M b c l result.
Definition source_context_conjunction_intro_formula :form :=
  ∀∀∀∀∀∀∀ (source_context_conjunction_formula $6 $5 $7 $4 →
    context_bounded_formula $6 $5 $7 $0 →context_bounded_formula $3 $2 $1 $0 →
    (∀ (context_member_formula $7 $6 $8 $0 →source_full_prv_formula $4 $3 $2 $0)) →
    (source_bounded_accept_formula $4 $0 ∧source_full_prv_formula $3 $2 $1 $4)).
Local Opaque holds source_context_conjunction_formula context_bounded_formula
  context_member_formula source_full_prv_formula source_bounded_accept_formula.
Lemma source_context_conjunction_intro_definable M :Definable1 M (source_context_conjunction_intro_at M).
Proof.
  exists source_context_conjunction_intro_formula,(fun _=>zeroM M). intro n.
  unfold source_context_conjunction_intro_formula,source_context_conjunction_intro_at.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  repeat setoid_rewrite holds_and.
  setoid_rewrite source_context_conjunction_formula_correct.
  setoid_rewrite context_bounded_formula_correct.
  setoid_rewrite context_member_formula_correct.
  setoid_rewrite source_full_prv_formula_correct.
  setoid_rewrite source_bounded_accept_formula_correct. reflexivity.
Qed.

Theorem source_context_conjunction_intro M :forall n,source_context_conjunction_intro_at M n.
Proof.
  apply (definable_induction M (source_context_conjunction_intro_at M)
    (source_context_conjunction_intro_definable M)).
  - intros sb sc result b c l k HResult HSource HTarget HH.
    apply source_context_conjunction_zero in HResult.
    assert (HResultBound:source_bounded M result k).
    { apply (proj2 (source_bounded_accept_binary M SFImpl (zeroM M)(zeroM M) result k
        (or_intror (or_intror eq_refl)) HResult)). split;apply source_bounded_accept_falsity. }
    split;[exact HResultBound|].
    destruct (environment_cons_total M b c l (zeroM M)) as [u [v [m HCons]]].
    assert (HNew:context_bounded M u v m k).
    { apply (proj2 (context_bounded_cons M b c l (zeroM M) u v m k HCons)).
      split;[apply source_bounded_accept_falsity|exact HTarget]. }
    apply (full_source_II M b c l (zeroM M)(zeroM M) result u v m);
      [exists k;auto| |exact HCons|exact HResult].
    apply full_source_Ctx;[exists k;split;[apply source_bounded_accept_falsity|exact HNew]|].
    apply (proj2 (context_member_cons M b c l (zeroM M) u v m (zeroM M) HCons)). now left.
  - intros n IH sb sc result b c l k HResult HSource HTarget HH.
    apply source_context_conjunction_succ in HResult.
    destruct HResult as [p [h [HP [HHLast HAnd]]]].
    assert (HSourcePrefix:context_bounded M sb sc n k).
    { intros a [i [HI HA]]. apply HSource. exists i. split;[|exact HA].
      exact (coding_lt_trans M i n (succM M n) HI (coding_lt_succ M n)). }
    assert (HMember:context_member M sb sc (succM M n) h).
    { exists n. split;[apply coding_lt_succ|exact HHLast]. }
    destruct (IH sb sc p b c l k HP HSourcePrefix HTarget) as [BP PP].
    { intros a [i [HI HA]]. apply HH. exists i. split;[|exact HA].
      exact (coding_lt_trans M i n (succM M n) HI (coding_lt_succ M n)). }
    pose proof (HSource h HMember) as BH.
    assert (BR:source_bounded M result k).
    { exact (proj2 (source_bounded_accept_binary M SFAnd p h result k (or_introl eq_refl) HAnd) (conj BP BH)). }
    split;[exact BR|]. exact (full_source_CI M b c l p h result
      (ex_intro _ k (conj BR HTarget)) PP (HH h HMember) HAnd).
Qed.

Theorem source_context_conjunction_bound M sb sc n result k :
  source_context_conjunction M sb sc n result ->context_bounded M sb sc n k ->source_bounded M result k.
Proof.
  intros HResult HC.
  assert (HH:forall h,context_member M sb sc n h ->source_full_prv M sb sc n h).
  { intros h HH. exact (full_source_Ctx M sb sc n h (ex_intro _ k (conj (HC h HH) HC)) HH). }
  exact (proj1 (source_context_conjunction_intro M n sb sc result sb sc n k HResult HC HC HH)).
Qed.

Definition source_context_conjunction_project_at M n :=forall sb sc result b c l k,
  source_context_conjunction M sb sc n result ->context_bounded M sb sc n k ->
  context_bounded M b c l k ->source_full_prv M b c l result ->
  forall h,context_member M sb sc n h ->source_full_prv M b c l h.
Definition source_context_conjunction_project_formula :form :=
  ∀∀∀∀∀∀∀ (source_context_conjunction_formula $6 $5 $7 $4 →
    context_bounded_formula $6 $5 $7 $0 →context_bounded_formula $3 $2 $1 $0 →
    source_full_prv_formula $3 $2 $1 $4 →
    ∀ (context_member_formula $7 $6 $8 $0 →source_full_prv_formula $4 $3 $2 $0)).
Lemma source_context_conjunction_project_definable M :Definable1 M (source_context_conjunction_project_at M).
Proof.
  exists source_context_conjunction_project_formula,(fun _=>zeroM M). intro n.
  unfold source_context_conjunction_project_formula,source_context_conjunction_project_at.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite source_context_conjunction_formula_correct.
  setoid_rewrite context_bounded_formula_correct.
  setoid_rewrite context_member_formula_correct.
  setoid_rewrite source_full_prv_formula_correct. reflexivity.
Qed.

Theorem source_context_conjunction_project M :forall n,source_context_conjunction_project_at M n.
Proof.
  apply (definable_induction M (source_context_conjunction_project_at M)
    (source_context_conjunction_project_definable M)).
  - intros sb sc result b c l k HResult HSource HTarget PResult h HH.
    exfalso. exact (context_empty M sb sc h HH).
  - intros n IH sb sc result b c l k HResult HSource HTarget PResult h [i [HI HH]].
    apply source_context_conjunction_succ in HResult.
    destruct HResult as [p [j [HP [HJ HAnd]]]].
    assert (HSourcePrefix:context_bounded M sb sc n k).
    { intros a [r [HR HA]]. apply HSource. exists r. split;[|exact HA].
      exact (coding_lt_trans M r n (succM M n) HR (coding_lt_succ M n)). }
    destruct (proj1 (coding_lt_succ_cases M i n) HI) as [HIn|E].
    + apply (IH sb sc p b c l k HP HSourcePrefix HTarget);[|exists i;auto].
      exact (full_source_CE1 M b c l p j result
        (ex_intro _ k (conj (source_context_conjunction_bound M sb sc n p k HP HSourcePrefix) HTarget)) PResult HAnd).
    + subst i. pose proof (beta_unique M sb sc n h j HH HJ) as E. subst h.
      assert (HMember:context_member M sb sc (succM M n) j) by (exists n;split;[apply coding_lt_succ|exact HJ]).
      exact (full_source_CE2 M b c l p j result
        (ex_intro _ k (conj (HSource j HMember) HTarget)) PResult HAnd).
Qed.

Print Assumptions source_context_conjunction_intro_definable.
Print Assumptions source_context_conjunction_intro.
Print Assumptions source_context_conjunction_bound.
Print Assumptions source_context_conjunction_project_definable.
Print Assumptions source_context_conjunction_project.
