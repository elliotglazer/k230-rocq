(** Concrete uses of the finite template compiler in an arbitrary PA model.
    These include projection of the actual guarded K axiom bundle. *)
From PAModel Require Import Model CodeExpressions NumericalProofs ProofClosure
  ProofTemplates TemplateCD TemplatePropositional.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Lemma template_core G a b c :
  In (c,a) G -> In (c,b) G -> template_proof G (E_k230 a b c).
Proof.
  intros Ha Hb. apply (template_discharge G).
  eapply template_der_andl. apply dthm.
  exact (TP_bundle a b c Ha Hb).
Qed.

Lemma template_vacuity G a b c :
  In (c,a) G -> In (c,b) G -> template_proof G (E_vacuity a b c).
Proof.
  intros Ha Hb. apply (template_discharge G).
  eapply template_der_andr. apply dthm.
  exact (TP_bundle a b c Ha Hb).
Qed.

Definition K_parameter_guards : list (code_expr * code_expr) :=
  [(CEvar 2,CEvar 0);(CEvar 2,CEvar 1)].

Lemma K_parameter_guards_correct M a b c : c <> a -> c <> b ->
  template_guards_hold M (code_parameters a b c (zeroM M)) K_parameter_guards.
Proof.
  intros Ha Hb p q H x y Hx Hy.
  destruct H as [H|[H|[]]]; inversion H; subst p q;
    cbn [code_relation code_parameters] in Hx,Hy; subst x y; assumption.
Qed.

Theorem numerical_K_core M a b c f : c <> a -> c <> b ->
  code_relation M (code_parameters a b c (zeroM M))
    (E_k230 (CEvar 0) (CEvar 1) (CEvar 2)) f ->
  numerically_provable M f.
Proof.
  intros Ha Hb Hf.
  apply (template_sound M (code_parameters a b c (zeroM M))
    K_parameter_guards (E_k230 (CEvar 0) (CEvar 1) (CEvar 2))
    (K_parameter_guards_correct M a b c Ha Hb)).
  - apply template_core; cbn; tauto.
  - exact Hf.
Qed.

Theorem numerical_K_vacuity M a b c f : c <> a -> c <> b ->
  code_relation M (code_parameters a b c (zeroM M))
    (E_vacuity (CEvar 0) (CEvar 1) (CEvar 2)) f ->
  numerically_provable M f.
Proof.
  intros Ha Hb Hf.
  apply (template_sound M (code_parameters a b c (zeroM M))
    K_parameter_guards (E_vacuity (CEvar 0) (CEvar 1) (CEvar 2))
    (K_parameter_guards_correct M a b c Ha Hb)).
  - apply template_vacuity; cbn; tauto.
  - exact Hf.
Qed.

Theorem numerical_K_B6a M a b c f : c <> a -> c <> b ->
  code_relation M (code_parameters a b c (zeroM M))
    (E_wa
      (E_wim (E_weq (CEvar 0) (CEvar 1))
        (E_wal (CEvar 2) (E_weq (CEvar 0) (CEvar 1))))
      (E_wim (E_wel (CEvar 0) (CEvar 1))
        (E_wal (CEvar 2) (E_wel (CEvar 0) (CEvar 1))))) f ->
  numerically_provable M f.
Proof.
  intros Ha Hb Hf.
  eapply (template_sound M (code_parameters a b c (zeroM M))
    K_parameter_guards _ (K_parameter_guards_correct M a b c Ha Hb));
    [apply (template_B6a K_parameter_guards (CEvar 0) (CEvar 1) (CEvar 2));
      cbn; tauto|exact Hf].
Qed.

Theorem numerical_K_explosion M :
  numerically_provable M (code_numeral M 1) ->
  forall f, numerically_provable M f.
Proof.
  intros Hfalse f.
  set (env := fun _ : nat => f).
  destruct (code_relation_total M (E_wim (CEconst 1) (CEvar 0)) env)
    as [h Hh].
  assert (Hp : numerically_provable M h).
  { apply (unguarded_template_sound M env (E_wim (CEconst 1) (CEvar 0)));
      [apply template_F|exact Hh]. }
  apply (numerical_mp M (code_numeral M 1) f h Hfalse Hp).
  exact (expression_implication_graph M env (CEconst 1) (CEvar 0)
    (code_numeral M 1) f h eq_refl eq_refl Hh).
Qed.

Print Assumptions numerical_K_core.
Print Assumptions numerical_K_vacuity.
Print Assumptions numerical_K_B6a.
Print Assumptions numerical_K_explosion.
