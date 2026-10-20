(** Universal specialization in the actual numerical K calculus.
    The proof program follows L1_LMeta.lall_ex/lspec. Its only nonlogical
    inputs are the already constructed Leibniz and output-vacuity proofs. *)
From PAModel Require Import Model FiniteCoding CodeExpressions CodeDescent
  NumericalProofs ProofTemplates TemplateCD TemplatePropositional
  ProofMacros QuantifierMacros NumericalEquality NumericalVacuitySteps
  NamedSubstitution NamedBinderFresh NamedLeibnizSteps NamedLeibniz
  NamedSubstitutionVacuity.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Lemma ns_macro_flip G inputs h a b :
  proof_macro G inputs (E_wim h (E_wim a b)) ->
  proof_macro G inputs (E_wim a (E_wim h b)).
Proof.
  intro H. apply macro_discharge,macro_deduction,macro_deduction.
  eapply md_mp with (a:=a);[apply md_hyp;cbn;auto|].
  eapply md_mp with (a:=h);[apply md_hyp;cbn;auto|].
  apply md_global;exact H.
Qed.

Lemma ns_macro_all_exists G inputs x p q :
  proof_macro G inputs
    (E_wim (E_wal x (E_wim p q)) (E_wim (E_wex x p) (E_wex x q))).
Proof.
  unfold E_wex.
  eapply macro_syl with (q:=E_wal x (E_wim (E_wn q) (E_wn p))).
  - apply macro_all_monotone,PM_template,template_contraposition.
  - eapply macro_syl with (q:=E_wim (E_wal x (E_wn q)) (E_wal x (E_wn p))).
    + apply PM_template,template_r2.
    + apply PM_template,template_contraposition.
Qed.

Lemma ns_macro_specialization x y a v :
  proof_macro nil
    (E_wim (E_weq x y) (E_wim a v) :: E_vac x v :: nil)
    (E_wim (E_wal x a) v).
Proof.
  set (inputs:=E_wim (E_weq x y) (E_wim a v) :: E_vac x v :: nil).
  assert (H1 : proof_macro nil inputs
    (E_wim (E_wal x a) (E_wal x (E_wim (E_weq x y) v)))).
  { apply macro_all_monotone,ns_macro_flip,PM_input;cbn;auto. }
  assert (H2 : proof_macro nil inputs
    (E_wim (E_wal x a) (E_wim (E_wex x (E_weq x y)) (E_wex x v)))).
  { eapply macro_syl;[exact H1|apply ns_macro_all_exists]. }
  assert (H3 : proof_macro nil inputs (E_wim (E_wal x a) (E_wex x v))).
  { eapply PM_mp;[|apply ns_macro_flip;exact H2].
    exact (PM_template _ (TP_row LR1 x y (CEconst 0) (CEconst 0))). }
  eapply macro_syl;[exact H3|].
  eapply macro_syl with (q:=E_wex x (E_wal x v)).
  - apply macro_exists_monotone,PM_input;cbn;auto.
  - apply PM_template,template_r6.
Qed.

Theorem numerical_named_specialization M f x y v allf result :
  x<>y -> named_binder_absent M f x -> named_binder_absent M f y ->
  named_substitution M f x y v ->
  universal_graph M x f allf -> implication_graph M allf v result ->
  numerically_provable M result.
Proof.
  intros Hxy Hx Hy Hv Hall Hresult.
  set (env:=code_parameters x y f v).
  destruct (code_relation_total M (E_weq (CEvar 0) (CEvar 1)) env) as [h Eh].
  assert (Hh : equality_graph M x y h).
  { exact (proj1 (expression_equality_graph M env (CEvar 0) (CEvar 1) x y h eq_refl eq_refl) Eh). }
  assert (Eall : code_relation M env (E_wal (CEvar 0) (CEvar 2)) allf).
  { exact (proj2 (expression_universal_iff M env (CEvar 0) (CEvar 2) x f allf eq_refl eq_refl) Hall). }
  assert (Eresult : code_relation M env (E_wim (E_wal (CEvar 0) (CEvar 2)) (CEvar 3)) result).
  { exact (proj2 (expression_implication_iff M env (E_wal (CEvar 0) (CEvar 2)) (CEvar 3)
      allf v result Eall eq_refl) Hresult). }
  apply (ns_proof_macro M env
    (E_wim (E_weq (CEvar 0) (CEvar 1)) (E_wim (CEvar 2) (CEvar 3)) ::
     E_vac (CEvar 0) (CEvar 3) :: nil)
    (E_wim (E_wal (CEvar 0) (CEvar 2)) (CEvar 3))).
  - intros e [<-|[<-|[]]].
    + apply (proj2 (ns_under_expression M env (E_weq (CEvar 0) (CEvar 1))
        (CEvar 2) (CEvar 3) h f v Eh eq_refl eq_refl)).
      exact (proj1 (named_leibniz_internal M f x y h v Hh Hx Hy Hv)).
    + intros q Hq. apply (numerical_named_substitution_vacuity M f x y v q Hxy Hx Hv).
      exact (proj1 (expression_vacuity_graph M env (CEvar 0) (CEvar 3) x v q eq_refl eq_refl) Hq).
  - apply ns_macro_specialization.
  - exact Eresult.
Qed.

Corollary numerical_named_specialization_total M f x y allf :
  x<>y -> named_binder_absent M f x -> named_binder_absent M f y ->
  universal_graph M x f allf ->
  exists v result,named_substitution M f x y v /\
    implication_graph M allf v result /\ numerically_provable M result.
Proof.
  intros Hxy Hx Hy Hall.
  destruct (named_substitution_binder_absent_total M f x y Hy) as [v Hv].
  destruct (code_relation_total M (E_wim (CEvar 0) (CEvar 1))
    (arguments2 allf v (zeroM M))) as [result Hresult].
  exists v,result. split;[exact Hv|]. split;[exact Hresult|].
  exact (numerical_named_specialization M f x y v allf result Hxy Hx Hy Hv Hall Hresult).
Qed.
