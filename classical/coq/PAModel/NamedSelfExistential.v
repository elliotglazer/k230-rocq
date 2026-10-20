(** Same-name existential introduction, with the same explicit inner-binder
    restriction as NamedSelfSpecialization. No syntactic substitution or
    semantic vacuity is assumed. *)
From PAModel Require Import Model Arithmetic FiniteCoding Pairing CodeExpressions
  NumericalProofs ProofTemplates TemplateCD TemplatePropositional ProofMacros
  QuantifierMacros NumericalVacuitySteps NamedLeibnizSteps NamedBinderFresh
  NamedBinderConstructors NamedSelfSpecialization NamedExistential.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Lemma named_binder_absent_one M x :
  named_binder_absent M (code_numeral M 1) x.
Proof.
  apply (named_binder_absent_membership M (zeroM M) (zeroM M)).
  exists (zeroM M). split;[apply pair_zero|].
  rewrite (Arithmetic.mul_comm M),Arithmetic.mul_zero,Arithmetic.add_zero.
  reflexivity.
Qed.

Lemma named_binder_absent_negation M f nf x :
  implication_graph M f (code_numeral M 1) nf ->
  named_binder_absent M f x -> named_binder_absent M nf x.
Proof.
  intros HN HX. eapply named_binder_absent_implication;
    [exact HN|exact HX|apply named_binder_absent_one].
Qed.

Lemma self_exists_double_negation G f :
  template_proof G (E_wim f (E_wn (E_wn f))).
Proof.
  apply template_discharge. do 2 apply template_deduction.
  eapply dmp;apply dhyp;cbn;tauto.
Qed.

Lemma self_exists_program G inputs x f :
  proof_macro G inputs (E_wim (E_wal x (E_wn f)) (E_wn f)) ->
  proof_macro G inputs (E_wim f (E_wex x f)).
Proof.
  intro H. unfold E_wex.
  eapply macro_syl;[apply PM_template,self_exists_double_negation|].
  exact (macro_contra G inputs _ _ H).
Qed.

Theorem numerical_named_self_exists_intro M f x exf result :
  named_binder_absent M f x -> named_exists_graph M x f exf ->
  implication_graph M f exf result -> numerically_provable M result.
Proof.
  intros HX HEx HResult. set (env:=x .: f .: fun _=>zeroM M).
  destruct (code_relation_total M (E_wn (CEvar 1)) env) as [nf HN].
  destruct (code_relation_total M (E_wal (CEvar 0) (E_wn (CEvar 1))) env)
    as [allnf HAll].
  assert (HNeg : implication_graph M f (code_numeral M 1) nf).
  { exact (proj1 (expression_implication_iff M env (CEvar 1) (CEconst 1)
      f (code_numeral M 1) nf eq_refl eq_refl) HN). }
  assert (HAbs : named_binder_absent M nf x).
  { exact (named_binder_absent_negation M f nf x HNeg HX). }
  assert (HAllGraph : universal_graph M x nf allnf).
  { exact (proj1 (expression_universal_iff M env (CEvar 0) (E_wn (CEvar 1))
      x nf allnf eq_refl HN) HAll). }
  assert (P : ns_proof M env
    (E_wim (E_wal (CEvar 0) (E_wn (CEvar 1))) (E_wn (CEvar 1)))).
  { intros p HP. apply (numerical_named_self_specialization M nf x allnf p HAbs HAllGraph).
    exact (proj1 (expression_implication_iff M env
      (E_wal (CEvar 0) (E_wn (CEvar 1))) (E_wn (CEvar 1))
      allnf nf p HAll HN) HP). }
  assert (PIntro : ns_proof M env (E_wim (CEvar 1) (E_wex (CEvar 0) (CEvar 1)))).
  { apply (ns_proof_macro M env
      (E_wim (E_wal (CEvar 0) (E_wn (CEvar 1))) (E_wn (CEvar 1)) :: nil)).
    - intros p [<-|[]]. exact P.
    - apply self_exists_program,PM_input;now left. }
  assert (HE : code_relation M env (E_wex (CEvar 0) (CEvar 1)) exf).
  { exact (proj2 (named_exists_expression M env (CEvar 0) (CEvar 1)
      x f exf eq_refl eq_refl) HEx). }
  apply PIntro.
  exact (proj2 (expression_implication_iff M env (CEvar 1)
    (E_wex (CEvar 0) (CEvar 1)) f exf result eq_refl HE) HResult).
Qed.

Print Assumptions numerical_named_self_exists_intro.
