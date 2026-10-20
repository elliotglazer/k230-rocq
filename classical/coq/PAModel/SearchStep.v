(** One exact enumerator step, expressed arithmetically in every PA model.
    The finite syntax compiler below does not iterate over model elements. *)
From PAModel Require Import Model Arithmetic FiniteCoding Pairing CodeExpressions.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Arith.PeanoNat Lists.List.
Unset Implicit Arguments.

Inductive search_pred : Type :=
| SPcode (target : nat) (expression : code_expr)
| SPand (p q : search_pred)
| SPor (p q : search_pred)
| SPnot (p : search_pred)
| SPexists (variable : nat) (body : search_pred).

Definition search_update {A : Type} (env : nat -> A) (v : nat) (x : A) :=
  fun i => if Nat.eq_dec i v then x else env i.

Fixpoint search_relation (M : Model) (env : nat -> carrier M) (p : search_pred) : Prop :=
  match p with
  | SPcode i e => code_relation M env e (env i)
  | SPand a b => search_relation M env a /\ search_relation M env b
  | SPor a b => search_relation M env a \/ search_relation M env b
  | SPnot a => ~search_relation M env a
  | SPexists v a => exists x, search_relation M (search_update env v x) a
  end.

Definition search_bind_terms (env : nat -> term) (v : nat) : nat -> term :=
  fun i => if Nat.eq_dec i v then $0 else (env i)`[↑].

Fixpoint search_formula (p : search_pred) (env : nat -> term) : form :=
  match p with
  | SPcode i e => code_formula e env (env i)
  | SPand a b => search_formula a env ∧ search_formula b env
  | SPor a b => search_formula a env ∨ search_formula b env
  | SPnot a => ¬search_formula a env
  | SPexists v a => ∃ search_formula a (search_bind_terms env v)
  end.

Lemma search_relation_ext M p env env' :
  (forall i, env i = env' i) ->
  (search_relation M env p <-> search_relation M env' p).
Proof.
  intro H. induction p in env,env',H |- *; cbn.
  - rewrite (H target). apply code_relation_ext. exact H.
  - rewrite (IHp1 env env' H),(IHp2 env env' H). reflexivity.
  - rewrite (IHp1 env env' H),(IHp2 env env' H). reflexivity.
  - rewrite (IHp env env' H). reflexivity.
  - split; intros [x Hx]; exists x.
    + assert (Hu : forall i, search_update env variable x i = search_update env' variable x i).
      { intro i. unfold search_update. destruct (Nat.eq_dec i variable); auto. }
      exact (proj1 (IHp _ _ Hu) Hx).
    + assert (Hu : forall i, search_update env variable x i = search_update env' variable x i).
      { intro i. unfold search_update. destruct (Nat.eq_dec i variable); auto. }
      exact (proj2 (IHp _ _ Hu) Hx).
Qed.

(** State values and all local numerical witnesses live in the model carrier. *)
Record search_state (A : Type) := mkSearchState {
  search_pl : A; search_np : A; search_tw : A;
  search_ws : A; search_d : A; search_h : A
}.
Arguments search_pl {A} _.
Arguments search_np {A} _.
Arguments search_tw {A} _.
Arguments search_ws {A} _.
Arguments search_d {A} _.
Arguments search_h {A} _.

Definition search_state_env M (s t : search_state (carrier M)) (i : nat) :=
  match i with
  | 0 => search_pl s | 1 => search_np s | 2 => search_tw s
  | 3 => search_ws s | 4 => search_d s | 5 => search_h s
  | 6 => search_pl t | 7 => search_np t | 8 => search_tw t
  | 9 => search_ws t | 10 => search_d t | 11 => search_h t
  | _ => zeroM M
  end.

Lemma search_bound_environment M rho env v x i :
  evalM M (x .: rho) (search_bind_terms env v i) =
  search_update (fun j => evalM M rho (env j)) v x i.
Proof.
  unfold search_bind_terms,search_update. destruct (Nat.eq_dec i v); [reflexivity|].
  unfold evalM. apply eval_up.
Qed.

Theorem search_formula_correct M p rho env :
  holds M rho (search_formula p env) <->
  search_relation M (fun i => evalM M rho (env i)) p.
Proof.
  induction p in rho,env |- *.
  - apply code_formula_correct.
  - change ((holds M rho (search_formula p1 env) /\ holds M rho (search_formula p2 env)) <->
      (search_relation M (fun i => evalM M rho (env i)) p1 /\ search_relation M (fun i => evalM M rho (env i)) p2)).
    rewrite IHp1,IHp2. reflexivity.
  - change ((holds M rho (search_formula p1 env) \/ holds M rho (search_formula p2 env)) <->
      (search_relation M (fun i => evalM M rho (env i)) p1 \/ search_relation M (fun i => evalM M rho (env i)) p2)).
    rewrite IHp1,IHp2. reflexivity.
  - change ((~holds M rho (search_formula p env)) <->
      ~search_relation M (fun i => evalM M rho (env i)) p).
    rewrite IHp. reflexivity.
  - change ((exists x, holds M (x .: rho) (search_formula p (search_bind_terms env variable))) <->
      exists x, search_relation M (search_update (fun i => evalM M rho (env i)) variable x) p).
    split; intros [x Hx]; exists x.
    + apply IHp in Hx.
      exact (proj1 (search_relation_ext M p _ _ (search_bound_environment M rho env variable x)) Hx).
    + apply IHp.
      exact (proj2 (search_relation_ext M p _ _ (search_bound_environment M rho env variable x)) Hx).
Qed.

(** Small finite constructors used only to display the exact step formula. *)
Fixpoint SPall (ps : list search_pred) : search_pred :=
  match ps with
  | nil => SPcode 0 (CEvar 0)
  | cons p nil => p
  | cons p rest => SPand p (SPall rest)
  end.
Fixpoint SPany (ps : list search_pred) : search_pred :=
  match ps with
  | nil => SPnot (SPcode 0 (CEvar 0))
  | cons p nil => p
  | cons p rest => SPor p (SPany rest)
  end.
Fixpoint SPbind (vs : list nat) (body : search_pred) : search_pred :=
  match vs with nil => body | cons v rest => SPexists v (SPbind rest body) end.

Definition SPsame i j := SPcode i (CEvar j).
Definition SPnum i n := SPcode i (CEconst n).
Definition SPsum i j k := SPcode i (CEadd (CEvar j) (CEvar k)).
Definition SPpair target a b := SPcode target (CEpair (CEvar a) (CEvar b)).

(** Slots 0..5 are pl,np,tw,ws,d,h before the step; 6..11 are after.
    Prefix-local slots: 12=pl1,13=np1,14=ac,15=pl2,16=x,17=pl3,18=d1.
    AX-local slots: 19=c,20=y,21=pl4,22=u,23=pl5,24=b.
    Named binders alter only their own slot; the compiler shifts all other
    terms automatically, including arbitrary formula parameters. *)
Import ListNotations.

Definition search_prefix : search_pred := SPall (SPor (SPall (SPnum 0 0 :: SPsame 12 1 :: SPcode 13 (CEadd (CEvar 1) (CEconst 1)) :: nil))
       (SPall (SPcode 0 (CEadd (CEvar 12) (CEconst 1)) :: SPsame 13 1 :: nil)) :: SPpair 12 14 15 :: SPpair 15 16 17 :: SPsum 18 4 16 :: nil).

Definition search_common : search_pred := SPall (SPsame 6 17 :: SPsame 7 13 :: SPsame 10 18 :: nil).

Definition search_mp : search_pred := SPall (SPnum 14 0 :: search_common :: SPnum 11 0 :: SPor
    (SPall (SPcode 5 (E_wim (CEvar 2) (CEvar 18)) :: SPsame 8 18 :: SPcode 9 (CEpair (CEconst 0) (CEvar 3)) :: nil))
    (SPall (SPnot (SPcode 5 (E_wim (CEvar 2) (CEvar 18))) :: SPnum 8 0 :: SPsame 9 3 :: nil)) :: nil).

Definition search_drop : search_pred := SPall (SPnum 14 1 :: search_common :: SPsame 8 5 :: SPpair 9 2 3 :: SPsame 11 5 :: nil).

Definition search_nip : search_pred := SPall (SPnum 14 2 :: SPnot (SPnum 5 1) :: search_common :: SPsame 8 2 :: SPpair 3 11 9 :: nil).

Definition E_ax_stack (a h b c u t w : code_expr) : code_expr :=
  CEpair (E_rho1 a b) (CEpair (E_rho2 a b c) (CEpair (E_rho3 a b c)
    (CEpair (E_rho4 a b c) (CEpair (E_rho5 a b c) (CEpair (E_rho6 a c)
      (CEpair (E_rho7 a b c) (CEpair (E_rho8 a b c u)
        (CEpair (E_wal a h) (CEpair t w))))))))).

Definition search_ax : search_pred := SPbind (19 :: 20 :: 21 :: 22 :: 23 :: 24 :: nil) (SPall (SPcode 14 (CEadd (CEvar 19) (CEconst 3)) :: SPpair 17 20 21 :: SPpair 21 22 23 :: SPsum 24 5 20 :: SPsame 6 23 :: SPsame 7 13 :: SPnum 10 0 :: SPnum 11 0 :: SPcode 9 (E_ax_stack (CEvar 18) (CEvar 5) (CEvar 24) (CEvar 19)
    (CEvar 22) (CEvar 2) (CEvar 3)) :: SPor (SPall (SPor (SPsame 19 18) (SPsame 19 24) :: SPnum 8 0 :: nil))
    (SPall (SPnot (SPsame 19 18) :: SPnot (SPsame 19 24) :: SPcode 8 (E_bundle (CEvar 18) (CEvar 24) (CEvar 19)) :: nil)) :: nil)).

Definition search_kernel : search_pred := SPany (search_mp :: search_drop :: search_nip :: search_ax :: nil).
Definition search_step_pred : search_pred :=
  SPbind (12 :: 13 :: 14 :: 15 :: 16 :: 17 :: 18 :: nil) (SPand search_prefix search_kernel).
Definition search_halt_pred : search_pred :=
  SPbind (12 :: 13 :: 14 :: 15 :: 16 :: 17 :: 18 :: nil) (SPall (search_prefix :: SPnum 14 2 :: SPnum 5 1 :: nil)).

Definition search_step_formula : form := search_formula search_step_pred var.
Definition search_halt_formula : form := search_formula search_halt_pred var.

Theorem search_step_formula_correct M rho :
  holds M rho search_step_formula <-> search_relation M rho search_step_pred.
Proof. apply search_formula_correct. Qed.
Theorem search_halt_formula_correct M rho :
  holds M rho search_halt_formula <-> search_relation M rho search_halt_pred.
Proof. apply search_formula_correct. Qed.

(** This equality pins the altered logical row as well as the exact stack order. *)
From K230L Require Enum230.
Theorem E_ax_stack_value env a h b c u t w :
  code_value env (E_ax_stack a h b c u t w) =
  Enum230.ax_stack (code_value env a) (code_value env h) (code_value env b)
    (code_value env c) (code_value env u) (code_value env t) (code_value env w).
Proof.
  unfold E_ax_stack,Enum230.ax_stack.
  cbn [code_value].
  rewrite !code_value_rho1,!code_value_rho2,!code_value_rho3,!code_value_rho4,
    !code_value_rho5,!code_value_rho6,!code_value_rho7,!code_value_rho8,!code_value_wal.
  reflexivity.
Qed.

Definition search_values M (xs : list (carrier M)) : nat -> carrier M :=
  fun i => nth i xs (zeroM M).
Definition search_implication M a b z :=
  code_relation M (search_values M (a :: b :: nil))
    (E_wim (CEvar 0) (CEvar 1)) z.
Definition search_bundle M a b c z :=
  code_relation M (search_values M (a :: b :: c :: nil))
    (E_bundle (CEvar 0) (CEvar 1) (CEvar 2)) z.
Definition search_stack M a h b c u t w z :=
  code_relation M (search_values M (a :: h :: b :: c :: u :: t :: w :: nil))
    (E_ax_stack (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3)
      (CEvar 4) (CEvar 5) (CEvar 6)) z.

Lemma search_implication_variables M env i j z :
  code_relation M env (E_wim (CEvar i) (CEvar j)) z <->
  search_implication M (env i) (env j) z.
Proof. reflexivity. Qed.
Lemma search_bundle_variables M env i j k z :
  code_relation M env (E_bundle (CEvar i) (CEvar j) (CEvar k)) z <->
  search_bundle M (env i) (env j) (env k) z.
Proof. reflexivity. Qed.
Lemma search_stack_variables M env a h b c u t w z :
  code_relation M env (E_ax_stack (CEvar a) (CEvar h) (CEvar b)
    (CEvar c) (CEvar u) (CEvar t) (CEvar w)) z <->
  search_stack M (env a) (env h) (env b) (env c) (env u) (env t) (env w) z.
Proof. reflexivity. Qed.

Lemma search_add_variables M env i j z :
  code_relation M env (CEadd (CEvar i) (CEvar j)) z <->
  z = addM M (env i) (env j).
Proof. cbn. split; [intros (x & y & -> & -> & H); exact H|].
  intro H. exists (env i),(env j). auto. Qed.
Lemma search_add_constant M env i n z :
  code_relation M env (CEadd (CEvar i) (CEconst n)) z <->
  z = addM M (env i) (code_numeral M n).
Proof. cbn. split; [intros (x & y & -> & -> & H); exact H|].
  intro H. exists (env i),(code_numeral M n). auto. Qed.
Lemma search_pair_variables M env i j z :
  code_relation M env (CEpair (CEvar i) (CEvar j)) z <->
  pair_graph M (env i) (env j) z.
Proof. cbn. split; [intros (x & y & -> & -> & H); exact H|].
  intro H. exists (env i),(env j). auto. Qed.
Lemma search_pair_zero M env j z :
  code_relation M env (CEpair (CEconst 0) (CEvar j)) z <->
  pair_graph M (zeroM M) (env j) z.
Proof. cbn. split; [intros (x & y & -> & -> & H); exact H|].
  intro H. exists (zeroM M),(env j). auto. Qed.
Lemma search_variable M env i z :
  code_relation M env (CEvar i) z <-> z = env i.
Proof. reflexivity. Qed.
Lemma search_constant M env n z :
  code_relation M env (CEconst n) z <-> z = code_numeral M n.
Proof. reflexivity. Qed.

Definition search_add_graph M a b z : Prop :=
  exists x y, x = a /\ y = b /\ z = addM M x y.
Definition search_pair_graph M a b z : Prop :=
  exists x y, x = a /\ y = b /\ pair_graph M x y z.
Lemma search_add_graph_correct M a b z :
  search_add_graph M a b z <-> z = addM M a b.
Proof. unfold search_add_graph. split; [intros (x & y & -> & -> & H); exact H|].
  intro H. exists a,b. auto. Qed.
Lemma search_pair_graph_correct M a b z :
  search_pair_graph M a b z <-> pair_graph M a b z.
Proof. unfold search_pair_graph. split; [intros (x & y & -> & -> & H); exact H|].
  intro H. exists a,b. auto. Qed.

Definition search_prefix_relation M (s : search_state (carrier M))
    pl1 np1 ac pl2 x pl3 d1 : Prop :=
  ((search_pl s = zeroM M /\ pl1 = search_np s /\
      search_add_graph M (search_np s) (code_numeral M 1) np1) \/
   (search_add_graph M pl1 (code_numeral M 1) (search_pl s) /\ np1 = search_np s)) /\
  search_pair_graph M ac pl2 pl1 /\ search_pair_graph M x pl3 pl2 /\
  search_add_graph M (search_d s) x d1.
Definition search_common_relation M (t : search_state (carrier M)) pl3 np1 d1 :=
  search_pl t = pl3 /\ search_np t = np1 /\ search_d t = d1.
Definition search_kernel_relation M (s t : search_state (carrier M)) pl3 np1 ac d1 : Prop :=
  (ac = zeroM M /\ search_common_relation M t pl3 np1 d1 /\
    search_h t = zeroM M /\
    ((search_implication M (search_tw s) d1 (search_h s) /\
        search_tw t = d1 /\ search_pair_graph M (zeroM M) (search_ws s) (search_ws t)) \/
     (~search_implication M (search_tw s) d1 (search_h s) /\
        search_tw t = zeroM M /\ search_ws t = search_ws s))) \/
  (ac = code_numeral M 1 /\ search_common_relation M t pl3 np1 d1 /\
    search_tw t = search_h s /\ search_pair_graph M (search_tw s) (search_ws s) (search_ws t) /\
    search_h t = search_h s) \/
  (ac = code_numeral M 2 /\ search_h s <> code_numeral M 1 /\
    search_common_relation M t pl3 np1 d1 /\ search_tw t = search_tw s /\
    search_pair_graph M (search_h t) (search_ws t) (search_ws s)) \/
  (exists c y pl4 u pl5 b,
    search_add_graph M c (code_numeral M 3) ac /\
    search_pair_graph M y pl4 pl3 /\ search_pair_graph M u pl5 pl4 /\ search_add_graph M (search_h s) y b /\
    search_pl t = pl5 /\ search_np t = np1 /\ search_d t = zeroM M /\ search_h t = zeroM M /\
    search_stack M d1 (search_h s) b c u (search_tw s) (search_ws s) (search_ws t) /\
    (((c = d1 \/ c = b) /\ search_tw t = zeroM M) \/
     (c <> d1 /\ c <> b /\ search_bundle M d1 b c (search_tw t)))).

Definition enumerator_step M (s t : search_state (carrier M)) : Prop :=
  exists pl1 np1 ac pl2 x pl3 d1,
    search_prefix_relation M s pl1 np1 ac pl2 x pl3 d1 /\
    search_kernel_relation M s t pl3 np1 ac d1.
Definition enumerator_halt M (s : search_state (carrier M)) : Prop :=
  exists pl1 np1 ac pl2 x pl3 d1,
    search_prefix_relation M s pl1 np1 ac pl2 x pl3 d1 /\
    ac = code_numeral M 2 /\ search_h s = code_numeral M 1.

Theorem search_step_relation_correct M s t :
  search_relation M (search_state_env M s t) search_step_pred <->
  enumerator_step M s t.
Proof. reflexivity. Qed.

Theorem search_halt_relation_correct M s t :
  search_relation M (search_state_env M s t) search_halt_pred <->
  enumerator_halt M s.
Proof. reflexivity. Qed.

Theorem enumerator_step_formula_correct M s t :
  holds M (search_state_env M s t) search_step_formula <-> enumerator_step M s t.
Proof. rewrite search_step_formula_correct. apply search_step_relation_correct. Qed.
Theorem enumerator_halt_formula_correct M s t :
  holds M (search_state_env M s t) search_halt_formula <-> enumerator_halt M s.
Proof. rewrite search_halt_formula_correct. apply search_halt_relation_correct. Qed.
Theorem enumerator_halt_cache M s :
  enumerator_halt M s -> search_h s = code_numeral M 1.
Proof. intros (? & ? & ? & ? & ? & ? & ? & _ & _ & H). exact H. Qed.


