(** Finite proof templates with arbitrary, possibly nonstandard, numerical
    parameters. A template is a genuine derivation from the frozen K230
    Hilbert rows. Its soundness constructs internally finite beta proofs.+    Induction on this finite template does not induct on model elements. *)
From PAModel Require Import Model CodeExpressions NumericalProofs ProofClosure.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Fixpoint code_subst (s : nat -> code_expr) (e : code_expr) : code_expr :=
  match e with
  | CEconst n => CEconst n
  | CEvar i => s i
  | CEadd a b => CEadd (code_subst s a) (code_subst s b)
  | CEmul a b => CEmul (code_subst s a) (code_subst s b)
  | CEpair a b => CEpair (code_subst s a) (code_subst s b)
  end.

Theorem code_subst_graph M env s values :
  (forall i, code_relation M env (s i) (values i)) ->
  forall e z, code_relation M env (code_subst s e) z <->
    code_relation M values e z.
Proof.
  intros H e. induction e; intro z; cbn [code_subst code_relation].
  - reflexivity.
  - split; intro Hz.
    + exact (code_relation_functional M (s i) env z (values i) Hz (H i)).
    + subst z. exact (H i).
  - setoid_rewrite IHe1. setoid_rewrite IHe2. reflexivity.
  - setoid_rewrite IHe1. setoid_rewrite IHe2. reflexivity.
  - setoid_rewrite IHe1. setoid_rewrite IHe2. reflexivity.
Qed.

Lemma parameter_graphs M env a b c u x y z v :
  code_relation M env a x -> code_relation M env b y ->
  code_relation M env c z -> code_relation M env u v ->
  forall i, code_relation M env (code_parameters a b c u i)
    (code_parameters x y z v i).
Proof. intros Ha Hb Hc Hu [|[|[|i]]]; assumption. Qed.

Lemma expression_implication_graph M env a b x y h :
  code_relation M env a x -> code_relation M env b y ->
  code_relation M env (E_wim a b) h -> implication_graph M x y h.
Proof.
  intros Ha Hb Hh. unfold implication_graph.
  change (code_relation M env
    (code_subst (arguments2 a b (CEconst 0))
      (E_wim (CEvar 0) (CEvar 1))) h) in Hh.
  assert (Hp : forall i, code_relation M env
    (arguments2 a b (CEconst 0) i) (arguments2 x y (zeroM M) i)).
  { intros [|[|i]]; [exact Ha|exact Hb|reflexivity]. }
  exact (proj1 (code_subst_graph M env
    (arguments2 a b (CEconst 0)) (arguments2 x y (zeroM M)) Hp _ _) Hh).
Qed.

Lemma expression_universal_graph M env a b x y h :
  code_relation M env a x -> code_relation M env b y ->
  code_relation M env (E_wal a b) h -> universal_graph M x y h.
Proof.
  intros Ha Hb Hh. unfold universal_graph.
  change (code_relation M env
    (code_subst (arguments2 a b (CEconst 0))
      (E_wal (CEvar 0) (CEvar 1))) h) in Hh.
  assert (Hp : forall i, code_relation M env
    (arguments2 a b (CEconst 0) i) (arguments2 x y (zeroM M) i)).
  { intros [|[|i]]; [exact Ha|exact Hb|reflexivity]. }
  exact (proj1 (code_subst_graph M env
    (arguments2 a b (CEconst 0)) (arguments2 x y (zeroM M)) Hp _ _) Hh).
Qed.

Inductive logical_row := LR1 | LR2 | LR3 | LR4 | LR5 | LR6 | LR7 | LR8.
Definition row_expression r :=
  match r with
  | LR1 => code_row1 | LR2 => code_row2 | LR3 => code_row3
  | LR4 => code_row4 | LR5 => code_row5 | LR6 => code_row6
  | LR7 => code_row7 | LR8 => code_row8
  end.

Lemma row_axiom M r x y z v f :
  code_relation M (code_parameters x y z v) (row_expression r) f ->
  K230_axiom_relation M f.
Proof.
  intro H. right. exists x,y,z,v. destruct r; cbn [row_expression] in H;
    unfold code_axiom_rows;
    [now left|right;now left|do 2 right;now left|do 3 right;now left|
     do 4 right;now left|do 5 right;now left|do 6 right;now left|
     do 7 right;now left].
Qed.

Lemma substituted_row_provable M env r a b c u f :
  code_relation M env
    (code_subst (code_parameters a b c u) (row_expression r)) f ->
  numerically_provable M f.
Proof.
  intro H.
  destruct (code_relation_total M a env) as [x Hx].
  destruct (code_relation_total M b env) as [y Hy].
  destruct (code_relation_total M c env) as [z Hz].
  destruct (code_relation_total M u env) as [v Hv].
  apply numerical_axiom. apply (row_axiom M r x y z v f).
  exact (proj1 (code_subst_graph M env (code_parameters a b c u)
    (code_parameters x y z v)
    (parameter_graphs M env a b c u x y z v Hx Hy Hz Hv)
    (row_expression r) f) H).
Qed.

Definition template_guards_hold M env (G : list (code_expr * code_expr)) :=
  forall a b, In (a,b) G -> forall x y,
    code_relation M env a x -> code_relation M env b y -> x <> y.

Inductive template_proof (G : list (code_expr * code_expr)) : code_expr -> Prop :=
| TP_true : template_proof G (CEconst 0)
| TP_mp a b : template_proof G a -> template_proof G (E_wim a b) ->
    template_proof G b
| TP_gen a h : template_proof G h -> template_proof G (E_wal a h)
| TP_row r a b c u : template_proof G
    (code_subst (code_parameters a b c u) (row_expression r))
| TP_bundle a b c : In (c,a) G -> In (c,b) G ->
    template_proof G (E_bundle a b c).

Arguments TP_true {G}.
Arguments TP_mp {G} a b _ _.
Arguments TP_gen {G} a h _.
Arguments TP_row {G} r a b c u.
Arguments TP_bundle {G} a b c _ _.

Theorem template_sound M env G e :
  template_guards_hold M env G -> template_proof G e ->
  forall f, code_relation M env e f -> numerically_provable M f.
Proof.
  intros HG HT. induction HT; intros f Hf.
  - change (f = zeroM M) in Hf. subst f. apply numerical_truth.
  - destruct (code_relation_total M a env) as [x Hx].
    destruct (code_relation_total M (E_wim a b) env) as [h Hh].
    exact (numerical_mp M x f h (IHHT1 x Hx) (IHHT2 h Hh)
      (expression_implication_graph M env a b x f h Hx Hf Hh)).
  - destruct (code_relation_total M a env) as [x Hx].
    destruct (code_relation_total M h env) as [y Hy].
    exact (numerical_gen M x y f (IHHT y Hy)
      (expression_universal_graph M env a h x y f Hx Hy Hf)).
  - exact (substituted_row_provable M env r a b c u f Hf).
  - destruct (code_relation_total M a env) as [x Hx].
    destruct (code_relation_total M b env) as [y Hy].
    destruct (code_relation_total M c env) as [z Hz].
    apply numerical_axiom. right. exists x,y,z,(zeroM M).
    do 8 right. split; [exact (HG c a H z x Hz Hx)|].
    split; [exact (HG c b H0 z y Hz Hy)|].
    change (code_relation M env
      (code_subst (code_parameters a b c (CEconst 0)) code_bundle) f) in Hf.
    exact (proj1 (code_subst_graph M env (code_parameters a b c (CEconst 0))
      (code_parameters x y z (zeroM M))
      (parameter_graphs M env a b c (CEconst 0) x y z (zeroM M)
        Hx Hy Hz eq_refl) code_bundle f) Hf).
Qed.

Lemma unguarded_template_sound M env e :
  template_proof [] e -> forall f,
  code_relation M env e f -> numerically_provable M f.
Proof. apply template_sound. intros a b H. inversion H. Qed.

Lemma template_r8 {G} a b c u : template_proof G (E_rho8 a b c u).
Proof. exact (TP_row LR8 a b c u). Qed.

Lemma template_r6 {G} a b : template_proof G (E_rho6 a b).
Proof. exact (TP_row LR6 a b (CEconst 0) (CEconst 0)). Qed.

Lemma template_r2 {G} a b c : template_proof G (E_rho2 a b c).
Proof. exact (TP_row LR2 a b c (CEconst 0)). Qed.

Print Assumptions code_subst_graph.
Print Assumptions template_sound.
Print Assumptions unguarded_template_sound.
