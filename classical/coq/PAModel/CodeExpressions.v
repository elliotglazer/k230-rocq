(** Numerical K230 code expressions and their graphs in ordinary PA.
    Pair nodes mean the exact dual-Cantor polynomial relation, not an
    uninterpreted operation or a totality assumption. *)
From PAModel Require Import Model Arithmetic FiniteCoding Pairing.
From FOL Require Import FullSyntax Arithmetics.
Import Vector.VectorNotations.
Unset Implicit Arguments.

Inductive code_expr : Type :=
| CEconst (n : nat)
| CEvar (i : nat)
| CEadd (a b : code_expr)
| CEmul (a b : code_expr)
| CEpair (a b : code_expr).

Fixpoint code_numeral (M : Model) (n : nat) : carrier M :=
  match n with 0 => zeroM M | S k => succM M (code_numeral M k) end.

Fixpoint code_relation (M : Model) (env : nat -> carrier M)
    (e : code_expr) (z : carrier M) : Prop :=
  match e with
  | CEconst n => z = code_numeral M n
  | CEvar i => z = env i
  | CEadd a b => exists x y, code_relation M env a x /\
      code_relation M env b y /\ z = addM M x y
  | CEmul a b => exists x y, code_relation M env a x /\
      code_relation M env b y /\ z = mulM M x y
  | CEpair a b => exists x y, code_relation M env a x /\
      code_relation M env b y /\ pair_graph M x y z
  end.

Definition code_lift2 (t : term) : term := t`[↑]`[↑].
Definition code_lift_env (env : nat -> term) : nat -> term :=
  fun i => code_lift2 (env i).

Fixpoint code_formula (e : code_expr) (env : nat -> term) (z : term) : form :=
  match e with
  | CEconst n => z == num n
  | CEvar i => z == env i
  | CEadd a b => ∃∃ (code_formula a (code_lift_env env) $1 ∧
      (code_formula b (code_lift_env env) $0 ∧ code_lift2 z == ($1 ⊕ $0)))
  | CEmul a b => ∃∃ (code_formula a (code_lift_env env) $1 ∧
      (code_formula b (code_lift_env env) $0 ∧ code_lift2 z == ($1 ⊗ $0)))
  | CEpair a b => ∃∃ (code_formula a (code_lift_env env) $1 ∧
      (code_formula b (code_lift_env env) $0 ∧ pair_formula $1 $0 (code_lift2 z)))
  end.

Lemma code_eval_num (M : Model) rho n :
  evalM M rho (num n) = code_numeral M n.
Proof. induction n; [reflexivity|]. change (succM M (evalM M rho (num n)) = succM M (code_numeral M n)). now rewrite IHn. Qed.

Lemma code_eval_lift2 (M : Model) rho x y t :
  evalM M (y .: x .: rho) (code_lift2 t) = evalM M rho t.
Proof. unfold evalM, code_lift2. now rewrite !eval_up. Qed.

Lemma code_relation_ext (M : Model) e env env' z :
  (forall i, env i = env' i) ->
  (code_relation M env e z <-> code_relation M env' e z).
Proof.
  intro H. induction e in z |- *; cbn.
  - reflexivity.
  - now rewrite H.
  - setoid_rewrite IHe1. setoid_rewrite IHe2. reflexivity.
  - setoid_rewrite IHe1. setoid_rewrite IHe2. reflexivity.
  - setoid_rewrite IHe1. setoid_rewrite IHe2. reflexivity.
Qed.

Lemma code_relation_lift_env (M : Model) e rho env x y z :
  code_relation M (fun i => evalM M (y .: x .: rho) (code_lift_env env i)) e z <->
  code_relation M (fun i => evalM M rho (env i)) e z.
Proof. apply code_relation_ext. intro i. apply code_eval_lift2. Qed.

Theorem code_formula_correct (M : Model) e rho env z :
  holds M rho (code_formula e env z) <->
  code_relation M (fun i => evalM M rho (env i)) e (evalM M rho z).
Proof.
  induction e in rho, env, z |- *.
  - change (evalM M rho z = evalM M rho (num n) <-> evalM M rho z = code_numeral M n).
    rewrite code_eval_num. reflexivity.
  - reflexivity.
  - cbn [code_formula].
    change ((exists x y, holds M (y .: x .: rho) (code_formula e1 (code_lift_env env) $1) /\
      holds M (y .: x .: rho) (code_formula e2 (code_lift_env env) $0) /\
      evalM M (y .: x .: rho) (code_lift2 z) = addM M x y) <-> code_relation M (fun i => evalM M rho (env i)) (CEadd e1 e2) (evalM M rho z)).
    setoid_rewrite IHe1. setoid_rewrite IHe2.
    setoid_rewrite code_relation_lift_env. setoid_rewrite code_eval_lift2. reflexivity.
  - cbn [code_formula].
    change ((exists x y, holds M (y .: x .: rho) (code_formula e1 (code_lift_env env) $1) /\
      holds M (y .: x .: rho) (code_formula e2 (code_lift_env env) $0) /\
      evalM M (y .: x .: rho) (code_lift2 z) = mulM M x y) <-> code_relation M (fun i => evalM M rho (env i)) (CEmul e1 e2) (evalM M rho z)).
    setoid_rewrite IHe1. setoid_rewrite IHe2.
    setoid_rewrite code_relation_lift_env. setoid_rewrite code_eval_lift2. reflexivity.
  - cbn [code_formula].
    change ((exists x y, holds M (y .: x .: rho) (code_formula e1 (code_lift_env env) $1) /\
      holds M (y .: x .: rho) (code_formula e2 (code_lift_env env) $0) /\
      holds M (y .: x .: rho) (pair_formula $1 $0 (code_lift2 z))) <-> code_relation M (fun i => evalM M rho (env i)) (CEpair e1 e2) (evalM M rho z)).
    setoid_rewrite IHe1. setoid_rewrite IHe2.
    setoid_rewrite pair_formula_correct.
    setoid_rewrite code_relation_lift_env. setoid_rewrite code_eval_lift2. reflexivity.
Qed.

Lemma code_relation_total (M : Model) e env : exists z, code_relation M env e z.
Proof.
  induction e; cbn.
  - eexists; reflexivity.
  - eexists; reflexivity.
  - destruct IHe1 as [x Hx], IHe2 as [y Hy]. exists (addM M x y), x, y. auto.
  - destruct IHe1 as [x Hx], IHe2 as [y Hy]. exists (mulM M x y), x, y. auto.
  - destruct IHe1 as [x Hx], IHe2 as [y Hy].
    destruct (pair_total M x y) as [z Hz]. exists z, x, y. auto.
Qed.

Lemma code_relation_functional (M : Model) e env z z' :
  code_relation M env e z -> code_relation M env e z' -> z = z'.
Proof.
  induction e in z,z' |- *; cbn; intros H H'.
  - congruence.
  - congruence.
  - destruct H as [x [y [Hx [Hy Hz]]]], H' as [x' [y' [Hx' [Hy' Hz']]]].
    specialize (IHe1 _ _ Hx Hx'). specialize (IHe2 _ _ Hy Hy'). congruence.
  - destruct H as [x [y [Hx [Hy Hz]]]], H' as [x' [y' [Hx' [Hy' Hz']]]].
    specialize (IHe1 _ _ Hx Hx'). specialize (IHe2 _ _ Hy Hy'). congruence.
  - destruct H as [x [y [Hx [Hy Hz]]]], H' as [x' [y' [Hx' [Hy' Hz']]]].
    specialize (IHe1 _ _ Hx Hx'). specialize (IHe2 _ _ Hy Hy'). subst x' y'.
    exact (pair_functional M x y z z' Hz Hz').
Qed.

(** These constructors follow K230S.KCode230 and K230L.Codes230 literally. *)
Definition E_wim a b := CEmul (CEconst 4) (CEpair a b).
Definition E_wel i j := CEadd (E_wim i j) (CEconst 1).
Definition E_wal i a := CEadd (E_wim i a) (CEconst 2).
Definition E_weq i j := CEadd (E_wim i j) (CEconst 3).
Definition E_wn a := E_wim a (CEconst 1).
Definition E_wa a b := E_wn (E_wim a (E_wn b)).
Definition E_wex x a := E_wn (E_wal x (E_wn a)).
Definition E_ksubset a b k := E_wal k (E_wim (E_wel k a) (E_wel k b)).
Definition E_krequest b k m := E_wal b (E_wim m (E_wex b (E_wa m (E_wel b k)))).
Definition E_kcore a b k m :=
  E_wex k (E_wa (E_wim m (E_wel b k))
    (E_wal b (E_wim (E_wel b k)
      (E_wex a (E_wa m (E_wal a (E_wim (E_ksubset a b k) (E_krequest b k m)))))))).
Definition E_k230 a b c := E_kcore a b c c.
Definition E_vacuity a b c :=
  E_wa (E_wim (E_wel a b) (E_wal c (E_wel a b)))
       (E_wim (E_weq a b) (E_wal c (E_weq a b))).
Definition E_bundle a b c := E_wa (E_k230 a b c) (E_vacuity a b c).
Definition E_rho8 a b c u := E_wim (E_wim (E_wim c u) a) (E_wim (E_wim a c) (E_wim b c)).
Definition E_rho7 a b c := E_wim (E_weq c a) (E_wim (E_weq c b) (E_weq a b)).
Definition E_rho6 a b := E_wim (E_wex a (E_wal a b)) b.
Definition E_rho5 a b c := E_wim (E_weq c a) (E_wim (E_wel c b) (E_wel a b)).
Definition E_rho4 a b c := E_wim (E_wal a (E_wal b c)) (E_wal b (E_wal a c)).
Definition E_rho3 a b c := E_wim (E_weq a b) (E_wim (E_wel c a) (E_wel c b)).
Definition E_rho2 a b c := E_wim (E_wal a (E_wim b c)) (E_wim (E_wal a b) (E_wal a c)).
Definition E_rho1 a b := E_wex a (E_weq a b).

(** The eight logical axiom rows and the guarded K bundle. *)
Definition code_row1 := E_rho1 (CEvar 0) (CEvar 1).
Definition code_row2 := E_rho2 (CEvar 0) (CEvar 1) (CEvar 2).
Definition code_row3 := E_rho3 (CEvar 0) (CEvar 1) (CEvar 2).
Definition code_row4 := E_rho4 (CEvar 0) (CEvar 1) (CEvar 2).
Definition code_row5 := E_rho5 (CEvar 0) (CEvar 1) (CEvar 2).
Definition code_row6 := E_rho6 (CEvar 0) (CEvar 1).
Definition code_row7 := E_rho7 (CEvar 0) (CEvar 1) (CEvar 2).
Definition code_row8 := E_rho8 (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3).
Definition code_bundle := E_bundle (CEvar 0) (CEvar 1) (CEvar 2).

Definition code_axiom_rows (M : Model) (env : nat -> carrier M) (z : carrier M) : Prop :=
  (code_relation M env code_row1 z \/ (code_relation M env code_row2 z \/ (code_relation M env code_row3 z \/ (code_relation M env code_row4 z \/ (code_relation M env code_row5 z \/ (code_relation M env code_row6 z \/ (code_relation M env code_row7 z \/ (code_relation M env code_row8 z \/ (env 2 <> env 0 /\ (env 2 <> env 1 /\ code_relation M env code_bundle z)))))))))).

Definition code_axiom_body (env : nat -> term) (z : term) : form :=
  (code_formula code_row1 env z ∨ (code_formula code_row2 env z ∨ (code_formula code_row3 env z ∨ (code_formula code_row4 env z ∨ (code_formula code_row5 env z ∨ (code_formula code_row6 env z ∨ (code_formula code_row7 env z ∨ (code_formula code_row8 env z ∨ ((¬ (env 2 == env 0)) ∧ ((¬ (env 2 == env 1)) ∧ code_formula code_bundle env z)))))))))).

Lemma code_holds_or (M : Model) rho a b :
  holds M rho (a ∨ b) <-> holds M rho a \/ holds M rho b.
Proof. reflexivity. Qed.
Lemma code_holds_and (M : Model) rho a b :
  holds M rho (a ∧ b) <-> holds M rho a /\ holds M rho b.
Proof. reflexivity. Qed.
Lemma code_holds_neq (M : Model) rho a b :
  holds M rho (¬ (a == b)) <-> evalM M rho a <> evalM M rho b.
Proof. reflexivity. Qed.

Lemma code_axiom_body_correct (M : Model) rho env z :
  holds M rho (code_axiom_body env z) <->
  code_axiom_rows M (fun i => evalM M rho (env i)) (evalM M rho z).
Proof.
  unfold code_axiom_body, code_axiom_rows.
  rewrite !code_holds_or, !code_holds_and, !code_holds_neq, !code_formula_correct.
  reflexivity.
Qed.

Lemma code_axiom_rows_ext (M : Model) env env' z :
  (forall i, env i = env' i) ->
  (code_axiom_rows M env z <-> code_axiom_rows M env' z).
Proof.
  intro H. unfold code_axiom_rows.
  rewrite (code_relation_ext M code_row1 env env' z H).
  rewrite (code_relation_ext M code_row2 env env' z H).
  rewrite (code_relation_ext M code_row3 env env' z H).
  rewrite (code_relation_ext M code_row4 env env' z H).
  rewrite (code_relation_ext M code_row5 env env' z H).
  rewrite (code_relation_ext M code_row6 env env' z H).
  rewrite (code_relation_ext M code_row7 env env' z H).
  rewrite (code_relation_ext M code_row8 env env' z H).
  rewrite (code_relation_ext M code_bundle env env' z H), (H 0), (H 1), (H 2).
  reflexivity.
Qed.

Definition code_parameters {D : Type} (a b c u : D) (i : nat) : D :=
  match i with 0 => a | 1 => b | 2 => c | _ => u end.
Definition code_parameter_terms (i : nat) : term :=
  match i with 0 => $3 | 1 => $2 | 2 => $1 | _ => $0 end.
Definition code_lift4 (z : term) : term := code_lift2 (code_lift2 z).

Definition K230_axiom_relation (M : Model) (z : carrier M) : Prop :=
  z = zeroM M \/ exists a b c u, code_axiom_rows M (code_parameters a b c u) z.

Definition K230_axiom_formula (z : term) : form :=
  (z == zero) ∨ (∃∃∃∃ code_axiom_body code_parameter_terms (code_lift4 z)).

Lemma code_eval_lift4 (M : Model) rho a b c u z :
  evalM M (u .: c .: b .: a .: rho) (code_lift4 z) = evalM M rho z.
Proof. unfold code_lift4. now rewrite !code_eval_lift2. Qed.

Lemma code_rows_parameters (M : Model) rho a b c u z :
  code_axiom_rows M
    (fun i => evalM M (u .: c .: b .: a .: rho) (code_parameter_terms i)) z <->
  code_axiom_rows M (code_parameters a b c u) z.
Proof.
  apply code_axiom_rows_ext. intros [|[|[|i]]]; reflexivity.
Qed.

Theorem K230_axiom_formula_correct (M : Model) rho z :
  holds M rho (K230_axiom_formula z) <-> K230_axiom_relation M (evalM M rho z).
Proof.
  unfold K230_axiom_formula, K230_axiom_relation.
  change ((evalM M rho z = zeroM M \/
    exists a b c u, holds M (u .: c .: b .: a .: rho)
      (code_axiom_body code_parameter_terms (code_lift4 z))) <->
    (evalM M rho z = zeroM M \/ exists a b c u,
      code_axiom_rows M (code_parameters a b c u) (evalM M rho z))).
  setoid_rewrite code_axiom_body_correct.
  setoid_rewrite code_eval_lift4. setoid_rewrite code_rows_parameters.
  reflexivity.
Qed.

(** Checked conformance to the actual frozen natural-number definitions. *)
From K230S Require KCode230.
From K230L Require Codes230.

Fixpoint code_value (env : nat -> nat) (e : code_expr) : nat :=
  match e with
  | CEconst n => n
  | CEvar i => env i
  | CEadd a b => code_value env a + code_value env b
  | CEmul a b => code_value env a * code_value env b
  | CEpair a b => KCode230.P (code_value env a) (code_value env b)
  end.

Local Opaque KCode230.P.

Lemma code_value_wim env a b :
  code_value env (E_wim a b) = KCode230.wim (code_value env a) (code_value env b).
Proof. reflexivity. Qed.

Lemma code_value_wel env a b :
  code_value env (E_wel a b) = KCode230.wel (code_value env a) (code_value env b).
Proof. reflexivity. Qed.

Lemma code_value_wal env a b :
  code_value env (E_wal a b) = KCode230.wal (code_value env a) (code_value env b).
Proof. reflexivity. Qed.

Lemma code_value_weq env a b :
  code_value env (E_weq a b) = KCode230.weq (code_value env a) (code_value env b).
Proof. reflexivity. Qed.

Lemma code_value_wn env a :
  code_value env (E_wn a) = KCode230.wn (code_value env a).
Proof. reflexivity. Qed.

Lemma code_value_wa env a b :
  code_value env (E_wa a b) = KCode230.wa (code_value env a) (code_value env b).
Proof. reflexivity. Qed.

Lemma code_value_wex env a b :
  code_value env (E_wex a b) = KCode230.wex (code_value env a) (code_value env b).
Proof. reflexivity. Qed.

Lemma code_value_ksubset env a b c :
  code_value env (E_ksubset a b c) = KCode230.ksubset (code_value env a) (code_value env b) (code_value env c).
Proof.
  unfold E_ksubset, KCode230.ksubset.
  repeat first [progress rewrite code_value_wim | progress rewrite code_value_wel | progress rewrite code_value_wal | progress rewrite code_value_weq | progress rewrite code_value_wn | progress rewrite code_value_wa | progress rewrite code_value_wex | progress rewrite code_value_krequest | progress rewrite code_value_kcore | progress rewrite code_value_k230 | progress rewrite code_value_vacuity].
  reflexivity.
Qed.

Lemma code_value_krequest env a b c :
  code_value env (E_krequest a b c) = KCode230.krequest (code_value env a) (code_value env b) (code_value env c).
Proof.
  unfold E_krequest, KCode230.krequest.
  repeat first [progress rewrite code_value_wim | progress rewrite code_value_wel | progress rewrite code_value_wal | progress rewrite code_value_weq | progress rewrite code_value_wn | progress rewrite code_value_wa | progress rewrite code_value_wex | progress rewrite code_value_ksubset | progress rewrite code_value_kcore | progress rewrite code_value_k230 | progress rewrite code_value_vacuity].
  reflexivity.
Qed.

Lemma code_value_kcore env a b c u :
  code_value env (E_kcore a b c u) = KCode230.kcore (code_value env a) (code_value env b) (code_value env c) (code_value env u).
Proof.
  unfold E_kcore, KCode230.kcore.
  repeat first [progress rewrite code_value_wim | progress rewrite code_value_wel | progress rewrite code_value_wal | progress rewrite code_value_weq | progress rewrite code_value_wn | progress rewrite code_value_wa | progress rewrite code_value_wex | progress rewrite code_value_ksubset | progress rewrite code_value_krequest | progress rewrite code_value_k230 | progress rewrite code_value_vacuity].
  reflexivity.
Qed.

Lemma code_value_k230 env a b c :
  code_value env (E_k230 a b c) = KCode230.k230 (code_value env a) (code_value env b) (code_value env c).
Proof.
  unfold E_k230, KCode230.k230.
  repeat first [progress rewrite code_value_wim | progress rewrite code_value_wel | progress rewrite code_value_wal | progress rewrite code_value_weq | progress rewrite code_value_wn | progress rewrite code_value_wa | progress rewrite code_value_wex | progress rewrite code_value_ksubset | progress rewrite code_value_krequest | progress rewrite code_value_kcore | progress rewrite code_value_vacuity].
  reflexivity.
Qed.

Lemma code_value_vacuity env a b c :
  code_value env (E_vacuity a b c) = KCode230.vacuity230 (code_value env a) (code_value env b) (code_value env c).
Proof.
  unfold E_vacuity, KCode230.vacuity230.
  repeat first [progress rewrite code_value_wim | progress rewrite code_value_wel | progress rewrite code_value_wal | progress rewrite code_value_weq | progress rewrite code_value_wn | progress rewrite code_value_wa | progress rewrite code_value_wex | progress rewrite code_value_ksubset | progress rewrite code_value_krequest | progress rewrite code_value_kcore | progress rewrite code_value_k230].
  reflexivity.
Qed.

Lemma code_value_bundle env a b c :
  code_value env (E_bundle a b c) = KCode230.bundle230 (code_value env a) (code_value env b) (code_value env c).
Proof.
  unfold E_bundle, KCode230.bundle230.
  repeat first [progress rewrite code_value_wim | progress rewrite code_value_wel | progress rewrite code_value_wal | progress rewrite code_value_weq | progress rewrite code_value_wn | progress rewrite code_value_wa | progress rewrite code_value_wex | progress rewrite code_value_ksubset | progress rewrite code_value_krequest | progress rewrite code_value_kcore | progress rewrite code_value_k230 | progress rewrite code_value_vacuity].
  reflexivity.
Qed.

Lemma code_value_rho1 env a b :
  code_value env (E_rho1 a b) = Codes230.rho1 (code_value env a) (code_value env b).
Proof.
  unfold E_rho1, Codes230.rho1.
  repeat first [progress rewrite code_value_wim | progress rewrite code_value_wel | progress rewrite code_value_wal | progress rewrite code_value_weq | progress rewrite code_value_wn | progress rewrite code_value_wa | progress rewrite code_value_wex | progress rewrite code_value_ksubset | progress rewrite code_value_krequest | progress rewrite code_value_kcore | progress rewrite code_value_k230 | progress rewrite code_value_vacuity].
  reflexivity.
Qed.

Lemma code_value_rho2 env a b c :
  code_value env (E_rho2 a b c) = Codes230.rho2 (code_value env a) (code_value env b) (code_value env c).
Proof.
  unfold E_rho2, Codes230.rho2.
  repeat first [progress rewrite code_value_wim | progress rewrite code_value_wel | progress rewrite code_value_wal | progress rewrite code_value_weq | progress rewrite code_value_wn | progress rewrite code_value_wa | progress rewrite code_value_wex | progress rewrite code_value_ksubset | progress rewrite code_value_krequest | progress rewrite code_value_kcore | progress rewrite code_value_k230 | progress rewrite code_value_vacuity].
  reflexivity.
Qed.

Lemma code_value_rho3 env a b c :
  code_value env (E_rho3 a b c) = Codes230.rho3 (code_value env a) (code_value env b) (code_value env c).
Proof.
  unfold E_rho3, Codes230.rho3.
  repeat first [progress rewrite code_value_wim | progress rewrite code_value_wel | progress rewrite code_value_wal | progress rewrite code_value_weq | progress rewrite code_value_wn | progress rewrite code_value_wa | progress rewrite code_value_wex | progress rewrite code_value_ksubset | progress rewrite code_value_krequest | progress rewrite code_value_kcore | progress rewrite code_value_k230 | progress rewrite code_value_vacuity].
  reflexivity.
Qed.

Lemma code_value_rho4 env a b c :
  code_value env (E_rho4 a b c) = Codes230.rho4 (code_value env a) (code_value env b) (code_value env c).
Proof.
  unfold E_rho4, Codes230.rho4.
  repeat first [progress rewrite code_value_wim | progress rewrite code_value_wel | progress rewrite code_value_wal | progress rewrite code_value_weq | progress rewrite code_value_wn | progress rewrite code_value_wa | progress rewrite code_value_wex | progress rewrite code_value_ksubset | progress rewrite code_value_krequest | progress rewrite code_value_kcore | progress rewrite code_value_k230 | progress rewrite code_value_vacuity].
  reflexivity.
Qed.

Lemma code_value_rho5 env a b c :
  code_value env (E_rho5 a b c) = Codes230.rho5 (code_value env a) (code_value env b) (code_value env c).
Proof.
  unfold E_rho5, Codes230.rho5.
  repeat first [progress rewrite code_value_wim | progress rewrite code_value_wel | progress rewrite code_value_wal | progress rewrite code_value_weq | progress rewrite code_value_wn | progress rewrite code_value_wa | progress rewrite code_value_wex | progress rewrite code_value_ksubset | progress rewrite code_value_krequest | progress rewrite code_value_kcore | progress rewrite code_value_k230 | progress rewrite code_value_vacuity].
  reflexivity.
Qed.

Lemma code_value_rho6 env a b :
  code_value env (E_rho6 a b) = Codes230.rho6 (code_value env a) (code_value env b).
Proof.
  unfold E_rho6, Codes230.rho6.
  repeat first [progress rewrite code_value_wim | progress rewrite code_value_wel | progress rewrite code_value_wal | progress rewrite code_value_weq | progress rewrite code_value_wn | progress rewrite code_value_wa | progress rewrite code_value_wex | progress rewrite code_value_ksubset | progress rewrite code_value_krequest | progress rewrite code_value_kcore | progress rewrite code_value_k230 | progress rewrite code_value_vacuity].
  reflexivity.
Qed.

Lemma code_value_rho7 env a b c :
  code_value env (E_rho7 a b c) = Codes230.rho7 (code_value env a) (code_value env b) (code_value env c).
Proof.
  unfold E_rho7, Codes230.rho7.
  repeat first [progress rewrite code_value_wim | progress rewrite code_value_wel | progress rewrite code_value_wal | progress rewrite code_value_weq | progress rewrite code_value_wn | progress rewrite code_value_wa | progress rewrite code_value_wex | progress rewrite code_value_ksubset | progress rewrite code_value_krequest | progress rewrite code_value_kcore | progress rewrite code_value_k230 | progress rewrite code_value_vacuity].
  reflexivity.
Qed.

Lemma code_value_rho8 env a b c u :
  code_value env (E_rho8 a b c u) = Codes230.rho8 (code_value env a) (code_value env b) (code_value env c) (code_value env u).
Proof.
  unfold E_rho8, Codes230.rho8.
  repeat first [progress rewrite code_value_wim | progress rewrite code_value_wel | progress rewrite code_value_wal | progress rewrite code_value_weq | progress rewrite code_value_wn | progress rewrite code_value_wa | progress rewrite code_value_wex | progress rewrite code_value_ksubset | progress rewrite code_value_krequest | progress rewrite code_value_kcore | progress rewrite code_value_k230 | progress rewrite code_value_vacuity].
  reflexivity.
Qed.

(** Stable interface for the numerical proof checker. *)
Definition axiom_formula := K230_axiom_formula.
Definition numeric_axiom := K230_axiom_relation.

Theorem axiom_formula_correct (M : Model) rho z :
  holds M rho (axiom_formula z) <-> numeric_axiom M (evalM M rho z).
Proof. exact (K230_axiom_formula_correct M rho z). Qed.

Lemma numeric_axiom_definable (M : Model) : Definable1 M (numeric_axiom M).
Proof.
  exists (axiom_formula $0), (fun _ => zeroM M).
  intro z. symmetry. apply axiom_formula_correct.
Qed.

Print Assumptions code_formula_correct.
Print Assumptions code_relation_total.
Print Assumptions code_relation_functional.
Print Assumptions K230_axiom_formula_correct.
Print Assumptions numeric_axiom_definable.
Print Assumptions code_value_bundle.
Print Assumptions code_value_rho8.
