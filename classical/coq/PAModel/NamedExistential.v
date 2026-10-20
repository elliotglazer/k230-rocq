(** Existential rules for the named K syntax.  Introduction uses the original
    substitution graph directly; no substitution into the chosen falsity code
    is required.  Elimination is a global implication to be used after guarded
    contextual generalization. *)
From PAModel Require Import Model FiniteCoding CodeExpressions CodeDescent
  NumericalProofs ProofTemplates TemplatePropositional ProofMacros QuantifierMacros
  NumericalEquality NumericalVacuitySteps NumericalVacuity FreshNames
  NamedSubstitution NamedBinderFresh NamedLeibnizSteps NamedLeibniz
  NamedSubstitutionVacuity NamedSpecialization NamedAlpha.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Definition named_exists_graph M x f e :=
  code_relation M (arguments2 x f (zeroM M)) (E_wex (CEvar 0) (CEvar 1)) e.
Definition named_exists_formula (x f e : term) : form :=
  code_formula (E_wex (CEvar 0) (CEvar 1)) (arguments2 x f zero) e.
Lemma named_exists_formula_correct M rho x f e :
  holds M rho (named_exists_formula x f e) <->
  named_exists_graph M (evalM M rho x) (evalM M rho f) (evalM M rho e).
Proof.
  unfold named_exists_formula,named_exists_graph. rewrite code_formula_correct.
  apply code_relation_ext. intros [|[|i]];reflexivity.
Qed.
Lemma named_exists_graph_total M x f : exists e,named_exists_graph M x f e.
Proof. apply code_relation_total. Qed.
Lemma named_exists_graph_functional M x f e e' :
  named_exists_graph M x f e -> named_exists_graph M x f e' -> e=e'.
Proof. apply code_relation_functional. Qed.
Lemma named_exists_expression M env X F x f e :
  code_relation M env X x -> code_relation M env F f ->
  (code_relation M env (E_wex X F) e <-> named_exists_graph M x f e).
Proof.
  intros HX HF. unfold named_exists_graph.
  change (code_relation M env
    (code_subst (arguments2 X F (CEconst 0)) (E_wex (CEvar 0) (CEvar 1))) e <->
    code_relation M (arguments2 x f (zeroM M)) (E_wex (CEvar 0) (CEvar 1)) e).
  apply code_subst_graph. intros [|[|i]];[exact HX|exact HF|reflexivity].
Qed.

Lemma ns_macro_exists_intro x y f v :
  proof_macro nil (E_wim (E_weq x y) (E_wim v f) :: E_vac x v :: nil)
    (E_wim v (E_wex x f)).
Proof.
  set (inputs:=E_wim (E_weq x y) (E_wim v f) :: E_vac x v :: nil).
  assert (H1 : proof_macro nil inputs (E_wim v (E_wal x (E_wim (E_weq x y) f)))).
  { eapply macro_syl with (q:=E_wal x v).
    - apply PM_input;cbn;auto.
    - apply macro_all_monotone,ns_macro_flip,PM_input;cbn;auto. }
  assert (H2 : proof_macro nil inputs (E_wim v (E_wim (E_wex x (E_weq x y)) (E_wex x f)))).
  { eapply macro_syl;[exact H1|apply ns_macro_all_exists]. }
  eapply PM_mp;[|apply ns_macro_flip;exact H2].
  exact (PM_template _ (TP_row LR1 x y (CEconst 0) (CEconst 0))).
Qed.

Theorem numerical_named_exists_intro M f x y v exf result :
  x<>y -> named_binder_absent M f x -> named_binder_absent M f y ->
  named_substitution M f x y v -> named_exists_graph M x f exf ->
  implication_graph M v exf result -> numerically_provable M result.
Proof.
  intros Hxy Hx Hy Hv Hex Hresult. set (env:=code_parameters x y f v).
  destruct (code_relation_total M (E_weq (CEvar 0) (CEvar 1)) env) as [h Eh].
  assert (Hh : equality_graph M x y h).
  { exact (proj1 (expression_equality_graph M env (CEvar 0) (CEvar 1) x y h eq_refl eq_refl) Eh). }
  assert (Eex : code_relation M env (E_wex (CEvar 0) (CEvar 2)) exf).
  { exact (proj2 (named_exists_expression M env (CEvar 0) (CEvar 2) x f exf eq_refl eq_refl) Hex). }
  apply (ns_proof_macro M env
    (E_wim (E_weq (CEvar 0) (CEvar 1)) (E_wim (CEvar 3) (CEvar 2)) ::
      E_vac (CEvar 0) (CEvar 3) :: nil)
    (E_wim (CEvar 3) (E_wex (CEvar 0) (CEvar 2)))).
  - intros e [<-|[<-|[]]].
    + apply (proj2 (ns_under_expression M env (E_weq (CEvar 0) (CEvar 1))
        (CEvar 3) (CEvar 2) h v f Eh eq_refl eq_refl)).
      exact (proj2 (named_leibniz_internal M f x y h v Hh Hx Hy Hv)).
    + intros q Hq. apply (numerical_named_substitution_vacuity M f x y v q Hxy Hx Hv).
      exact (proj1 (expression_vacuity_graph M env (CEvar 0) (CEvar 3) x v q eq_refl eq_refl) Hq).
  - apply ns_macro_exists_intro.
  - exact (proj2 (expression_implication_iff M env (CEvar 3) (E_wex (CEvar 0) (CEvar 2))
      v exf result eq_refl Eex) Hresult).
Qed.

Theorem numerical_named_exists_intro_total M f x y :
  x<>y -> named_binder_absent M f x -> named_binder_absent M f y ->
  exists v exf result,named_substitution M f x y v /\ named_exists_graph M x f exf /\
    implication_graph M v exf result /\ numerically_provable M result.
Proof.
  intros Hxy Hx Hy.
  destruct (named_substitution_binder_absent_total M f x y Hy) as [v Hv].
  destruct (named_exists_graph_total M x f) as [exf Hex].
  destruct (code_relation_total M (E_wim (CEvar 0) (CEvar 1))
    (arguments2 v exf (zeroM M))) as [result Hresult].
  exists v,exf,result. split;[exact Hv|]. split;[exact Hex|]. split;[exact Hresult|].
  exact (numerical_named_exists_intro M f x y v exf result Hxy Hx Hy Hv Hex Hresult).
Qed.

Lemma ns_macro_exists_elimination x f g :
  proof_macro nil (E_vac x g :: nil)
    (E_wim (E_wal x (E_wim f g)) (E_wim (E_wex x f) g)).
Proof.
  assert (Hcollapse : proof_macro nil (E_vac x g :: nil) (E_wim (E_wex x g) g)).
  { eapply macro_syl with (q:=E_wex x (E_wal x g)).
    - apply macro_exists_monotone,PM_input;cbn;auto.
    - apply PM_template,template_r6. }
  apply macro_discharge,macro_deduction,macro_deduction.
  eapply md_mp with (a:=E_wex x g);[|apply md_global;exact Hcollapse].
  eapply md_mp with (a:=E_wex x f);[apply md_hyp;cbn;auto|].
  eapply md_mp with (a:=E_wal x (E_wim f g));[apply md_hyp;cbn;auto|].
  apply md_global,ns_macro_all_exists.
Qed.

Lemma ns_proof_exists_elimination M env X F G :
  ns_proof M env (E_vac X G) ->
  ns_proof M env (E_wim (E_wal X (E_wim F G)) (E_wim (E_wex X F) G)).
Proof.
  intro H. apply (ns_proof_macro M env (E_vac X G :: nil)).
  - intros p [<-|[]];exact H.
  - apply ns_macro_exists_elimination.
Qed.
