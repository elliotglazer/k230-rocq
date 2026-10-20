(** Finite proof-building programs with already proved numerical inputs.
    Generalization is allowed on these inputs because they denote global
    theorems, not temporary hypotheses. Local deduction below still forbids
    generalization of its temporary hypotheses. *)
From PAModel Require Import Model CodeExpressions NumericalProofs ProofClosure
  ProofTemplates TemplateCD TemplatePropositional.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Inductive proof_macro (G : list (code_expr * code_expr)) (Inputs : list code_expr) : code_expr -> Prop :=
| PM_template e : template_proof G e -> proof_macro G Inputs e
| PM_input e : In e Inputs -> proof_macro G Inputs e
| PM_mp a b : proof_macro G Inputs a -> proof_macro G Inputs (E_wim a b) -> proof_macro G Inputs b
| PM_gen x a : proof_macro G Inputs a -> proof_macro G Inputs (E_wal x a).
Arguments PM_template {G Inputs} e _.
Arguments PM_input {G Inputs} e _.
Arguments PM_mp {G Inputs} a b _ _.
Arguments PM_gen {G Inputs} x a _.

Definition macro_inputs_proved M env Inputs :=
  forall e, In e Inputs -> forall f, code_relation M env e f -> numerically_provable M f.

Theorem proof_macro_sound M env G Inputs e :
  template_guards_hold M env G -> macro_inputs_proved M env Inputs ->
  proof_macro G Inputs e -> forall f, code_relation M env e f -> numerically_provable M f.
Proof.
  intros HG HI H. induction H; intros f Hf.
  - exact (template_sound M env G e HG H f Hf).
  - exact (HI e H f Hf).
  - destruct (code_relation_total M a env) as [u Hu].
    destruct (code_relation_total M (E_wim a b) env) as [h Hh].
    exact (numerical_mp M u f h (IHproof_macro1 u Hu) (IHproof_macro2 h Hh)
      (expression_implication_graph M env a b u f h Hu Hf Hh)).
  - destruct (code_relation_total M x env) as [v Hv].
    destruct (code_relation_total M a env) as [u Hu].
    exact (numerical_gen M v u f (IHproof_macro u Hu)
      (expression_universal_graph M env x a v u f Hv Hu Hf)).
Qed.

Lemma unguarded_macro_sound M env Inputs e : macro_inputs_proved M env Inputs ->
  proof_macro [] Inputs e -> forall f, code_relation M env e f -> numerically_provable M f.
Proof. apply proof_macro_sound. intros a b H. inversion H. Qed.

Lemma macro_one_input M env e u : code_relation M env e u -> numerically_provable M u ->
  macro_inputs_proved M env [e].
Proof.
  intros He Hu f [Hf|[]] v Hv. subst f.
  assert (v=u) by exact (code_relation_functional M e env v u Hv He). now subst v.
Qed.

Lemma macro_two_inputs M env e f u v :
  code_relation M env e u -> code_relation M env f v ->
  numerically_provable M u -> numerically_provable M v -> macro_inputs_proved M env [e;f].
Proof.
  intros He Hf Hu Hv g [Hg|[Hg|[]]] w Hw; subst g.
  - assert (w=u) by exact (code_relation_functional M e env w u Hw He). now subst w.
  - assert (w=v) by exact (code_relation_functional M f env w v Hw Hf). now subst w.
Qed.

Section Deduction.
Variable G : list (code_expr * code_expr).
Variable Inputs : list code_expr.

Inductive macro_derivation (Delta : list code_expr) : code_expr -> Prop :=
| md_hyp e : In e Delta -> macro_derivation Delta e
| md_global e : proof_macro G Inputs e -> macro_derivation Delta e
| md_mp a b : macro_derivation Delta a -> macro_derivation Delta (E_wim a b) -> macro_derivation Delta b.

Lemma macro_weaken Delta Delta' e : macro_derivation Delta e -> incl Delta Delta' -> macro_derivation Delta' e.
Proof.
  intros H HI. induction H as [e He|e He|a b _ IHa _ IHb].
  - apply md_hyp. exact (HI e He).
  - apply md_global. exact He.
  - exact (md_mp Delta' a b IHa IHb).
Qed.

Lemma macro_deduction Delta h e : macro_derivation (h::Delta) e -> macro_derivation Delta (E_wim h e).
Proof.
  induction 1 as [e [He|He]|e He|a b _ IHa _ IHb].
  - subst e. apply md_global, PM_template, template_I.
  - eapply md_mp; [apply md_hyp;exact He|]. apply md_global, PM_template, template_K.
  - eapply md_mp; [apply md_global;exact He|]. apply md_global, PM_template, template_K.
  - eapply md_mp; [exact IHa|]. eapply md_mp; [exact IHb|].
    apply md_global, PM_template, template_S.
Qed.

Lemma macro_discharge e : macro_derivation [] e -> proof_macro G Inputs e.
Proof.
  induction 1 as [e []|e H|a b _ IHa _ IHb]; [exact H|exact (PM_mp a b IHa IHb)].
Qed.
End Deduction.

Print Assumptions proof_macro_sound.
Print Assumptions macro_deduction.
