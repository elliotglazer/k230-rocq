(** * Std_setbase: basic set theory in the library's minimal signature (ND derivations).

    All lemmas are stated for an arbitrary context [G] with [incl ZF0base G] (equality axioms,
    extensionality, empty set, pairing, union, power set).  Set operations are predicates on terms
    ("HOAS" style, [Arguments ... : simpl never]); each has a substitution lemma in the rewrite
    database [fsub], so [simp] normalizes instances. *)
From Coq Require Import Arith Lia List.
From OldUndecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_tr Std_gen Std_iface Std_setnd.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.
#[local] Set Default Proof Using "All".

Ltac psubst P := intros; unfold P; repeat progress (cbn; autorewrite with fsub); fix_up; reflexivity.

(** ** Library predicates: substitution lemmas *)
#[global] Arguments is_eset : simpl never.
#[global] Arguments is_pair : simpl never.
#[global] Arguments is_union : simpl never.
#[global] Arguments sub' : simpl never.
#[global] Arguments is_power : simpl never.
#[global] Arguments is_sigma : simpl never.
#[global] Arguments is_inductive : simpl never.
#[global] Arguments is_om : simpl never.

Lemma sub'_subst x y s : (sub' x y)[s] = sub' x`[s] y`[s].
Proof. psubst sub'. Qed.
Lemma is_eset_subst x s : (is_eset x)[s] = is_eset x`[s].
Proof. psubst is_eset. Qed.
Lemma is_pair_subst x y z s : (is_pair x y z)[s] = is_pair x`[s] y`[s] z`[s].
Proof. psubst is_pair. Qed.
Lemma is_union_subst x y s : (is_union x y)[s] = is_union x`[s] y`[s].
Proof. psubst is_union. Qed.
Lemma is_power_subst x y s : (is_power x y)[s] = is_power x`[s] y`[s].
Proof. unfold is_power. cbn. rewrite !sub'_subst. cbn. now autorewrite with fsub. Qed.
Lemma is_sigma_subst x y s : (is_sigma x y)[s] = is_sigma x`[s] y`[s].
Proof. psubst is_sigma. Qed.
#[global] Hint Rewrite sub'_subst is_eset_subst is_pair_subst is_union_subst is_power_subst is_sigma_subst : fsub.
Lemma is_inductive_subst x s : (is_inductive x)[s] = is_inductive x`[s].
Proof. psubst is_inductive. Qed.
#[global] Hint Rewrite is_inductive_subst : fsub.
Lemma is_om_subst x s : (is_om x)[s] = is_om x`[s].
Proof. psubst is_om. Qed.
#[global] Hint Rewrite is_om_subst : fsub.

(** ** Axioms in the context *)
Section Ax.
Context (G : list form) (HG : incl ZF0base G).

Lemma in_refl : In ax_refl' G.   Proof. apply HG. cbn; tauto. Qed.
Lemma in_sym : In ax_sym' G.     Proof. apply HG. cbn; tauto. Qed.
Lemma in_trans : In ax_trans' G. Proof. apply HG. cbn; tauto. Qed.
Lemma in_eq_elem : In ax_eq_elem' G. Proof. apply HG. cbn; tauto. Qed.
Lemma in_ext : In ax_ext' G.     Proof. apply HG. cbn; tauto. Qed.
Lemma in_eset : In ax_eset' G.   Proof. apply HG. cbn; tauto. Qed.
Lemma in_pair : In ax_pair' G.   Proof. apply HG. cbn; tauto. Qed.
Lemma in_union : In ax_union' G. Proof. apply HG. cbn; tauto. Qed.
Lemma in_power : In ax_power' G. Proof. apply HG. cbn; tauto. Qed.

(** ** Equality *)
Lemma eq_refl' x : G ⊢C x ≡' x.
Proof. assert (H : G ⊢C ax_refl') by (apply Ctx, in_refl). finst H x. exact H. Qed.

Lemma eq_sym' x y : G ⊢C x ≡' y -> G ⊢C y ≡' x.
Proof. intros H1. assert (H : G ⊢C ax_sym') by (apply Ctx, in_sym). finst H x y. now fmp H H1. Qed.

Lemma eq_trans' x y z : G ⊢C x ≡' y -> G ⊢C y ≡' z -> G ⊢C x ≡' z.
Proof.
  intros H1 H2. assert (H : G ⊢C ax_trans') by (apply Ctx, in_trans). finst H x y z.
  fmp H H1. now fmp H H2.
Qed.

Lemma elem_cong x y x' y' : G ⊢C x ≡' x' -> G ⊢C y ≡' y' -> G ⊢C x ∈' y -> G ⊢C x' ∈' y'.
Proof.
  intros H1 H2 H3. assert (H : G ⊢C ax_eq_elem') by (apply Ctx, in_eq_elem).
  finst H x y x'. finst H y'. fmp H H1. fmp H H2. now fmp H H3.
Qed.

Lemma elem_l x x' y : G ⊢C x ≡' x' -> G ⊢C x ∈' y -> G ⊢C x' ∈' y.
Proof. intros H1 H2. eapply elem_cong; [exact H1| apply eq_refl' | exact H2]. Qed.

Lemma elem_r x y y' : G ⊢C y ≡' y' -> G ⊢C x ∈' y -> G ⊢C x ∈' y'.
Proof. intros H1 H2. eapply elem_cong; [apply eq_refl' | exact H1 | exact H2]. Qed.

Lemma ext_rule x y : G ⊢C sub' x y -> G ⊢C sub' y x -> G ⊢C x ≡' y.
Proof.
  intros H1 H2. assert (H : G ⊢C ax_ext') by (apply Ctx, in_ext). finst H x y.
  fmp H H1. now fmp H H2.
Qed.

End Ax.

(** ** Leibniz substitution *)
Lemma leib_gen (phi : form) : forall G (sg tau : nat -> term), incl ZF0base G ->
  (forall n, G ⊢C sg n ≡' tau n) -> G ⊢C phi[sg] -> G ⊢C phi[tau].
Proof.
  induction phi as [| P v | op a IHa b IHb | q a IHa] using form_ind_falsity;
    intros G sg tau HG Hst H.
  - exact H.
  - destruct P; cbn in v |- *; rewrite (vec2 v) in H |- *; cbn in *;
      destruct (Vector.hd v) as [n|[]]; destruct (Vector.hd (Vector.tl v)) as [m|[]]; cbn in *.
    + eapply elem_cong; eauto.
    + eapply eq_trans'; [exact HG| |]. apply eq_sym'; [exact HG|]. apply Hst.
      eapply eq_trans'; eauto.
  - assert (Hts : forall n, G ⊢C tau n ≡' sg n) by (intros n; apply eq_sym'; auto).
    destruct op; cbn in H |- *.
    + apply CI; [eapply IHa|eapply IHb]; eauto; [eapply CE1|eapply CE2]; exact H.
    + apply (DE H).
      * apply DI1. eapply IHa; [| |apply Ctx; now left]. now apply incl_cons_r.
        intros n. apply weak_cons, Hst.
      * apply DI2. eapply IHb; [| |apply Ctx; now left]. now apply incl_cons_r.
        intros n. apply weak_cons, Hst.
    + apply II. eapply IHb; [now apply incl_cons_r| intros n; apply weak_cons, Hst|].
      eapply IE; [apply weak_cons, H|]. eapply IHa; [now apply incl_cons_r| intros n; apply weak_cons, Hts|].
      apply Ctx; now left.
  - destruct q; cbn in H |- *.
    + apply AllI_named. intros t. apply (AllE t) in H. rewrite up_inst_form in H |- *.
      eapply IHa; [exact HG| |exact H]. intros [|n]; cbn; [apply eq_refl'; exact HG|]. apply Hst.
    + apply (ExE_named H). intros t. rewrite up_inst_form. apply (ExI t). rewrite up_inst_form.
      eapply IHa; [now apply incl_cons_r| |apply Ctx; now left].
      intros [|n]; cbn; [apply eq_refl'; now apply incl_cons_r|]. apply weak_cons, Hst.
Qed.

Lemma leib G (phi : form) x y : incl ZF0base G -> G ⊢C x ≡' y -> G ⊢C phi[x..] -> G ⊢C phi[y..].
Proof.
  intros HG Hxy H. eapply leib_gen; [exact HG| |exact H]. intros [|n]; cbn; [exact Hxy|]. now apply eq_refl'.
Qed.

(** rewrite a fact / the goal along an equation; [phi] is the formula with the rewritten
    position abstracted as [$0] (other terms shifted) *)
Ltac frew_in Heq phi H :=
  let HG := match goal with HG : incl ZF0base _ |- _ => constr:(HG) end in
  let H' := fresh in
  first [ pose proof (leib _ phi _ _ HG Heq) as H'; simp_in H'; specialize (H' H)
        | pose proof (leib _ phi _ _ HG (eq_sym' _ HG _ _ Heq)) as H'; simp_in H'; specialize (H' H) ];
  clear H; rename H' into H.
Ltac frew Heq phi :=
  let HG := match goal with HG : incl ZF0base _ |- _ => constr:(HG) end in
  let H' := fresh in
  first [ pose proof (leib _ phi _ _ HG Heq) as H'; simp_in H'; apply H'; clear H'
        | pose proof (leib _ phi _ _ HG (eq_sym' _ HG _ _ Heq)) as H'; simp_in H'; apply H'; clear H' ].

(** ** Separation and replacement instances *)
Lemma fb_forall_times_inv n : forall (psi : form) N, fb (n + N) psi -> fb N (forall_times n psi).
Proof.
  induction n as [|n IH]; intros psi N H; [exact H|].
  unfold forall_times. cbn [iter]. rewrite iter_switch. apply (IH (∀ psi)). cbn.
  eapply fb_mono; [exact H|lia].
Qed.

Lemma sep_closed n (phi : form) : fb (S n) phi -> closedf (forall_times n (ax_sep' phi)).
Proof.
  intros H. unfold closedf. apply fb_forall_times_inv. rewrite Nat.add_0_r. cbn.
  repeat split; try lia; (eapply fb_subst; [exact H|]); intros [|i] Hi; cbn; lia.
Qed.

Lemma rep_closed n (phi : form) : fb (S (S n)) phi -> closedf (forall_times n (ax_rep' phi)).
Proof.
  intros H. unfold closedf. apply fb_forall_times_inv. rewrite Nat.add_0_r. cbn.
  repeat split; try lia; eapply fb_subst; try exact H; intros [|[|i]] Hi; cbn; lia.
Qed.

Lemma sep_use G n (phi : form) (sg : nat -> term) x :
  In (forall_times n (ax_sep' phi)) G -> fb (S n) phi ->
  G ⊢C ∃ ∀ ($0 ∈' $1 ↔ $0 ∈' x`[↑]`[↑] ∧ phi[$0 .: (fun k => (sg k)`[↑]`[↑])]).
Proof.
  intros Hin Hfb. assert (H : G ⊢C forall_times n (ax_sep' phi)) by now apply Ctx.
  apply (closed_inst _ _ _ sg (sep_closed _ _ Hfb)) in H. apply (AllE x) in H. cbn in H.
  replace (phi[$0 .: (fun k => (sg k)`[↑]`[↑])]) with (phi[$0 .: Nat.add 3 >> var][up (up (up sg))][up (up x..)])
    by form_subst_eq.
  exact H.
Qed.

Lemma rep_use G n (phi : form) (sg : nat -> term) x :
  In (forall_times n (ax_rep' phi)) G -> fb (S (S n)) phi ->
  (forall a b b', G ⊢C phi[a .: b .: sg] → phi[a .: b' .: sg] → b ≡' b') ->
  G ⊢C ∃ ∀ ($0 ∈' $1 ↔ ∃ ($0 ∈' x`[↑]`[↑]`[↑] ∧ phi[$0 .: $1 .: (fun k => (sg k)`[↑]`[↑]`[↑])])).
Proof.
  intros Hin Hfb Hfun. assert (H : G ⊢C forall_times n (ax_rep' phi)) by now apply Ctx.
  apply (closed_inst _ _ _ sg (rep_closed _ _ Hfb)) in H. unfold ax_rep' in H. cbn [subst_form] in H.
  assert (Hf : G ⊢C (fun_rel' phi)[sg]).
  { unfold fun_rel'. cbn. apply AllI_named; intros a. apply AllI_named; intros b. apply AllI_named; intros b'.
    cbn. specialize (Hfun a b b').
    replace (phi[a .: b .: sg]) with (phi[$2 .: $1 .: Nat.add 3 >> var][up (up (up sg))][up (up a..)][up b..][b'..]) in Hfun by form_subst_eq.
    replace (phi[a .: b' .: sg]) with (phi[$2 .: $0 .: Nat.add 3 >> var][up (up (up sg))][up (up a..)][up b..][b'..]) in Hfun by form_subst_eq.
    rewrite subst_term_shift. exact Hfun. }
  pose proof (IE H Hf) as H'. clear H Hf.
  apply (AllE x) in H'. cbn in H'.
  replace (phi[$0 .: $1 .: (fun k => (sg k)`[↑]`[↑]`[↑])])
    with (phi[$0 .: $1 .: Nat.add 4 >> var][up (up (up (up sg)))][up (up (up x..))]) by form_subst_eq.
  exact H'.
Qed.

Arguments eq_refl' {G} HG x.
Arguments eq_sym' {G} HG x y.
Arguments eq_trans' {G} HG x y z.
Arguments elem_cong {G} HG x y x' y'.
Arguments elem_l {G} HG x x' y.
Arguments elem_r {G} HG x y y'.
Arguments ext_rule {G} HG x y.

(** ** Automation for equality and membership goals *)
Ltac getHG := match goal with H : incl ZF0base _ |- _ => constr:(H) end.

Ltac feq_at n :=
  let HG := getHG in
  match goal with
  | |- _ ⊢C ?a ≡' ?a => apply (eq_refl' HG)
  | H : _ ⊢C ?a ≡' ?b |- _ ⊢C ?a ≡' ?b => exact H
  | H : _ ⊢C ?b ≡' ?a |- _ ⊢C ?a ≡' ?b => exact (eq_sym' HG _ _ H)
  | _ => match n with
        | S ?m =>
          match goal with
          | H : _ ⊢C ?a ≡' ?c |- _ ⊢C ?a ≡' ?b => apply (eq_trans' HG a c b H); feq_at m
          | H : _ ⊢C ?c ≡' ?a |- _ ⊢C ?a ≡' ?b => apply (eq_trans' HG a c b (eq_sym' HG _ _ H)); feq_at m
          end
        end
  end.
Ltac feq := feq_at 3.

Ltac fmem :=
  let HG := getHG in
  match goal with
  | H : _ ⊢C ?a ∈' ?b |- _ ⊢C ?a ∈' ?b => exact H
  | H : _ ⊢C ?c ∈' ?d |- _ ⊢C ?a ∈' ?b => apply (elem_cong HG c d a b); [feq|feq|exact H]
  end.

(** ** Set predicates *)
Definition Sing (x s : term) : form := ∀ ($0 ∈' s`[↑] ↔ $0 ≡' x`[↑]).
Definition BUn (x y u : term) : form := ∀ ($0 ∈' u`[↑] ↔ $0 ∈' x`[↑] ∨ $0 ∈' y`[↑]).
Definition Adj (f p g : term) : form := ∀ ($0 ∈' g`[↑] ↔ $0 ∈' f`[↑] ∨ $0 ≡' p`[↑]).
Definition OP (x y p : term) : form := ∀ ($0 ∈' p`[↑] ↔ Sing x`[↑] $0 ∨ is_pair x`[↑] y`[↑] $0).
Definition App (f u v : term) : form := ∃ (OP u`[↑] v`[↑] $0 ∧ $0 ∈' f`[↑]).
#[global] Arguments Sing : simpl never.
#[global] Arguments BUn : simpl never.
#[global] Arguments Adj : simpl never.
#[global] Arguments OP : simpl never.
#[global] Arguments App : simpl never.

Lemma Sing_subst x s sg : (Sing x s)[sg] = Sing x`[sg] s`[sg].
Proof. psubst Sing. Qed.
Lemma BUn_subst x y u sg : (BUn x y u)[sg] = BUn x`[sg] y`[sg] u`[sg].
Proof. psubst BUn. Qed.
Lemma Adj_subst x y u sg : (Adj x y u)[sg] = Adj x`[sg] y`[sg] u`[sg].
Proof. psubst Adj. Qed.
#[global] Hint Rewrite Sing_subst BUn_subst Adj_subst : fsub.
Lemma OP_subst x y u sg : (OP x y u)[sg] = OP x`[sg] y`[sg] u`[sg].
Proof. psubst OP. Qed.
#[global] Hint Rewrite OP_subst : fsub.
Lemma App_subst x y u sg : (App x y u)[sg] = App x`[sg] y`[sg] u`[sg].
Proof. psubst App. Qed.
#[global] Hint Rewrite App_subst : fsub.

(** ** Empty set, pairs, singletons *)
Section Sets.
Context {G : list form} (HG : incl ZF0base G).

Lemma eset_ex : G ⊢C ∃ is_eset $0.
Proof. apply Ctx, in_eset, HG. Qed.

Lemma eset_el e z : G ⊢C is_eset e -> G ⊢C z ∈' e -> G ⊢C ⊥.
Proof. intros H Hz. finst H z. exact (IE H Hz). Qed.

Lemma pair_ex x y : G ⊢C ∃ is_pair x`[↑] y`[↑] $0.
Proof. assert (H : G ⊢C ax_pair') by (apply Ctx, in_pair, HG). finst H x y. exact H. Qed.

Lemma pair_el x y p z : G ⊢C is_pair x y p -> G ⊢C z ∈' p -> G ⊢C z ≡' x ∨ z ≡' y.
Proof. intros H Hz. finst H z. exact (iff_l _ _ _ H Hz). Qed.

Lemma pair_in x y p z : G ⊢C is_pair x y p -> G ⊢C z ≡' x ∨ z ≡' y -> G ⊢C z ∈' p.
Proof. intros H Hz. finst H z. exact (iff_r _ _ _ H Hz). Qed.

Lemma pair_l x y p : G ⊢C is_pair x y p -> G ⊢C x ∈' p.
Proof. intros H. apply (pair_in x y p x H). apply DI1, (eq_refl' HG). Qed.

Lemma pair_r x y p : G ⊢C is_pair x y p -> G ⊢C y ∈' p.
Proof. intros H. apply (pair_in x y p y H). apply DI2, (eq_refl' HG). Qed.

Lemma sing_el x s z : G ⊢C Sing x s -> G ⊢C z ∈' s -> G ⊢C z ≡' x.
Proof. intros H Hz. unfold Sing in H. finst H z. exact (iff_l _ _ _ H Hz). Qed.

Lemma sing_in' x s z : G ⊢C Sing x s -> G ⊢C z ≡' x -> G ⊢C z ∈' s.
Proof. intros H Hz. unfold Sing in H. finst H z. exact (iff_r _ _ _ H Hz). Qed.

Lemma sing_in x s : G ⊢C Sing x s -> G ⊢C x ∈' s.
Proof. intros H. apply (sing_in' x s x H), (eq_refl' HG). Qed.

Lemma sing_inj x y s : G ⊢C Sing x s -> G ⊢C Sing y s -> G ⊢C x ≡' y.
Proof. intros H1 H2. apply (sing_el y s x H2), (sing_in x s H1). Qed.

End Sets.

Lemma sing_ex {G} (HG : incl ZF0base G) x : G ⊢C ∃ Sing x`[↑] $0.
Proof.
  fobtain (pair_ex HG x x) as p Hp. fexists p. unfold Sing. fall z. fsplit.
  - fintro Hz. fhave H : (pair_el HG x x p z Hp Hz). fcases H H1 H2; feq.
  - fintro Hz. fhave H : (pair_l HG x x p Hp). fmem.
Qed.

Section Sets2.
Context {G : list form} (HG : incl ZF0base G).

Lemma ext_char (phi : form) a b :
  G ⊢C ∀ ($0 ∈' a`[↑] ↔ phi) -> G ⊢C ∀ ($0 ∈' b`[↑] ↔ phi) -> G ⊢C a ≡' b.
Proof.
  intros H1 H2. apply (ext_rule HG); unfold sub'; fall z; fintro Hz; finst H1 z; finst H2 z.
  - exact (iff_r _ _ _ H2 (iff_l _ _ _ H1 Hz)).
  - exact (iff_r _ _ _ H1 (iff_l _ _ _ H2 Hz)).
Qed.

Lemma sing_unique x s s' : G ⊢C Sing x s -> G ⊢C Sing x s' -> G ⊢C s ≡' s'.
Proof. unfold Sing. apply ext_char. Qed.

Lemma pair_unique x y p p' : G ⊢C is_pair x y p -> G ⊢C is_pair x y p' -> G ⊢C p ≡' p'.
Proof. unfold is_pair. apply ext_char. Qed.

Lemma union_ex x : G ⊢C ∃ is_union x`[↑] $0.
Proof. assert (H : G ⊢C ax_union') by (apply Ctx, in_union, HG). finst H x. exact H. Qed.

Lemma union_el x u z : G ⊢C is_union x u -> G ⊢C z ∈' u -> G ⊢C ∃ ($0 ∈' x`[↑] ∧ z`[↑] ∈' $0).
Proof. intros H Hz. unfold is_union in H. finst H z. exact (iff_l _ _ _ H Hz). Qed.

Lemma union_in x u y z : G ⊢C is_union x u -> G ⊢C y ∈' x -> G ⊢C z ∈' y -> G ⊢C z ∈' u.
Proof.
  intros H Hy Hz. unfold is_union in H. finst H z. apply (iff_r _ _ _ H). fexists y. fsplit; assumption.
Qed.

Lemma union_unique x u u' : G ⊢C is_union x u -> G ⊢C is_union x u' -> G ⊢C u ≡' u'.
Proof. unfold is_union. apply ext_char. Qed.

Lemma bun_el x y u z : G ⊢C BUn x y u -> G ⊢C z ∈' u -> G ⊢C z ∈' x ∨ z ∈' y.
Proof. intros H Hz. unfold BUn in H. finst H z. exact (iff_l _ _ _ H Hz). Qed.

Lemma bun_in x y u z : G ⊢C BUn x y u -> G ⊢C z ∈' x ∨ z ∈' y -> G ⊢C z ∈' u.
Proof. intros H Hz. unfold BUn in H. finst H z. exact (iff_r _ _ _ H Hz). Qed.

Lemma adj_el f p g z : G ⊢C Adj f p g -> G ⊢C z ∈' g -> G ⊢C z ∈' f ∨ z ≡' p.
Proof. intros H Hz. unfold Adj in H. finst H z. exact (iff_l _ _ _ H Hz). Qed.

Lemma adj_in f p g z : G ⊢C Adj f p g -> G ⊢C z ∈' f ∨ z ≡' p -> G ⊢C z ∈' g.
Proof. intros H Hz. unfold Adj in H. finst H z. exact (iff_r _ _ _ H Hz). Qed.

Lemma adj_in_l f p g z : G ⊢C Adj f p g -> G ⊢C z ∈' f -> G ⊢C z ∈' g.
Proof. intros H Hz. apply (adj_in f p g z H), DI1, Hz. Qed.

Lemma adj_in_r f p g : G ⊢C Adj f p g -> G ⊢C p ∈' g.
Proof. intros H. apply (adj_in f p g p H), DI2, (eq_refl' HG). Qed.

Lemma succ_el x s z : G ⊢C is_sigma x s -> G ⊢C z ∈' s -> G ⊢C z ∈' x ∨ z ≡' x.
Proof. intros H Hz. unfold is_sigma in H. finst H z. exact (iff_l _ _ _ H Hz). Qed.

Lemma succ_in x s z : G ⊢C is_sigma x s -> G ⊢C z ∈' x ∨ z ≡' x -> G ⊢C z ∈' s.
Proof. intros H Hz. unfold is_sigma in H. finst H z. exact (iff_r _ _ _ H Hz). Qed.

Lemma succ_in_l x s z : G ⊢C is_sigma x s -> G ⊢C z ∈' x -> G ⊢C z ∈' s.
Proof. intros H Hz. apply (succ_in x s z H), DI1, Hz. Qed.

Lemma succ_self x s : G ⊢C is_sigma x s -> G ⊢C x ∈' s.
Proof. intros H. apply (succ_in x s x H), DI2, (eq_refl' HG). Qed.

Lemma succ_unique x s s' : G ⊢C is_sigma x s -> G ⊢C is_sigma x s' -> G ⊢C s ≡' s'.
Proof. unfold is_sigma. apply ext_char. Qed.

Lemma adj_unique f p g g' : G ⊢C Adj f p g -> G ⊢C Adj f p g' -> G ⊢C g ≡' g'.
Proof. unfold Adj. apply ext_char. Qed.

End Sets2.

Lemma bun_ex {G} (HG : incl ZF0base G) x y : G ⊢C ∃ BUn x`[↑] y`[↑] $0.
Proof.
  fobtain (pair_ex HG x y) as p Hp. fobtain (union_ex HG p) as u Hu. fexists u. unfold BUn. fall z. fsplit.
  - fintro Hz. fhave H : (union_el HG p u z Hu Hz). fex H w Hw. fdestr Hw Hw1 Hw2.
    fhave H : (pair_el HG x y p w Hp Hw1). fcases H H1 H2.
    + fleft. fmem.
    + fright. fmem.
  - fintro Hz. fcases Hz H1 H2.
    + apply (union_in HG p u x z Hu); [apply (pair_l HG x y p Hp)|exact H1].
    + apply (union_in HG p u y z Hu); [apply (pair_r HG x y p Hp)|exact H2].
Qed.

Lemma adj_ex {G} (HG : incl ZF0base G) f p : G ⊢C ∃ Adj f`[↑] p`[↑] $0.
Proof.
  fobtain (sing_ex HG p) as s Hs. fobtain (bun_ex HG f s) as g Hg. fexists g. unfold Adj. fall z. fsplit.
  - fintro Hz. fhave H : (bun_el HG f s g z Hg Hz). fcases H H1 H2.
    + fleft. exact H1.
    + fright. exact (sing_el HG p s z Hs H2).
  - fintro Hz. apply (bun_in HG f s g z Hg). fcases Hz H1 H2.
    + fleft. exact H1.
    + fright. exact (sing_in' HG p s z Hs H2).
Qed.

Lemma succ_ex {G} (HG : incl ZF0base G) x : G ⊢C ∃ is_sigma x`[↑] $0.
Proof. exact (adj_ex HG x x). Qed.

(** ** Ordered pairs *)
Lemma op_ex {G} (HG : incl ZF0base G) x y : G ⊢C ∃ OP x`[↑] y`[↑] $0.
Proof.
  fobtain (sing_ex HG x) as s Hs. fobtain (pair_ex HG x y) as t Ht. fobtain (pair_ex HG s t) as p Hp.
  fexists p. unfold OP. fall z. fsplit.
  - fintro Hz. fhave H : (pair_el HG s t p z Hp Hz). fcases H H1 H2.
    + fleft. frew_in H1 (Sing x`[↑] $0) Hs. exact Hs.
    + fright. frew_in H2 (is_pair x`[↑] y`[↑] $0) Ht. exact Ht.
  - fintro Hz. apply (pair_in HG s t p z Hp). fcases Hz H1 H2.
    + fleft. exact (sing_unique HG x z s H1 Hs).
    + fright. exact (pair_unique HG x y z t H2 Ht).
Qed.

Lemma op_el {G} (HG : incl ZF0base G) x y p z : G ⊢C OP x y p -> G ⊢C z ∈' p -> G ⊢C Sing x z ∨ is_pair x y z.
Proof. intros H Hz. unfold OP in H. finst H z. exact (iff_l _ _ _ H Hz). Qed.

Lemma op_in {G} (HG : incl ZF0base G) x y p z : G ⊢C OP x y p -> G ⊢C Sing x z ∨ is_pair x y z -> G ⊢C z ∈' p.
Proof. intros H Hz. unfold OP in H. finst H z. exact (iff_r _ _ _ H Hz). Qed.

Lemma op_inj1 {G} (HG : incl ZF0base G) x y x' y' p : G ⊢C OP x y p -> G ⊢C OP x' y' p -> G ⊢C x ≡' x'.
Proof.
  intros H1 H2. fobtain (sing_ex HG x) as s Hs.
  fhave Hsp : (op_in HG x y p s H1 (DI1 _ Hs)). fhave H : (op_el HG x' y' p s H2 Hsp).
  fassert Hx' : (x' ∈' s).
  { fcases H Ha Hb; [exact (sing_in HG x' s Ha)|exact (pair_l HG x' y' s Hb)]. }
  apply (eq_sym' HG). exact (sing_el HG x s x' Hs Hx').
Qed.

Lemma op_inj2 {G} (HG : incl ZF0base G) x y x' y' p : G ⊢C OP x y p -> G ⊢C OP x' y' p -> G ⊢C y ≡' y'.
Proof.
  intros H1 H2. fhave Hxx : (op_inj1 HG x y x' y' p H1 H2).
  fobtain (pair_ex HG x y) as t Ht.
  fhave Htp : (op_in HG x y p t H1 (DI2 _ Ht)).
  fhave H : (op_el HG x' y' p t H2 Htp).
  fcases H Ha Hb.
  - fhave Hy : (pair_r HG x y t Ht). fhave Hyx : (sing_el HG x' t y Ha Hy).
    fobtain (pair_ex HG x' y') as t' Ht'.
    fhave Htp' : (op_in HG x' y' p t' H2 (DI2 _ Ht')).
    fhave H : (op_el HG x y p t' H1 Htp').
    fhave Hy' : (pair_r HG x' y' t' Ht').
    fcases H Hc Hd.
    + fhave E : (sing_el HG x t' y' Hc Hy'). feq.
    + fhave E : (pair_el HG x y t' y' Hd Hy'). fcases E E1 E2; feq.
  - fhave Hy : (pair_r HG x y t Ht). fhave E : (pair_el HG x' y' t y Hb Hy).
    fhave Hy' : (pair_r HG x' y' t Hb). fhave E' : (pair_el HG x y t y' Ht Hy').
    fcases E E1 E2.
    + fcases E' E3 E4; feq.
    + feq.
Qed.

Lemma op_inj {G} (HG : incl ZF0base G) x y x' y' p p' :
  G ⊢C OP x y p -> G ⊢C OP x' y' p' -> G ⊢C p ≡' p' -> G ⊢C x ≡' x' ∧ y ≡' y'.
Proof.
  intros H1 H2 E. frew_in E (OP x'`[↑] y'`[↑] $0) H2.
  fsplit; [exact (op_inj1 HG x y x' y' p H1 H2) | exact (op_inj2 HG x y x' y' p H1 H2)].
Qed.

(** ** Relations given by sets of ordered pairs *)
Lemma app_intro {G} (HG : incl ZF0base G) f u v p : G ⊢C OP u v p -> G ⊢C p ∈' f -> G ⊢C App f u v.
Proof. intros H1 H2. unfold App. fexists p. fsplit; assumption. Qed.

Lemma app_ex {G} (HG : incl ZF0base G) f u v : G ⊢C App f u v -> G ⊢C ∃ (OP u`[↑] v`[↑] $0 ∧ $0 ∈' f`[↑]).
Proof. intros H. exact H. Qed.

Lemma app_adj_el {G} (HG : incl ZF0base G) f q g u v :
  G ⊢C Adj f q g -> G ⊢C App g u v -> G ⊢C App f u v ∨ OP u v q.
Proof.
  intros Hg H. unfold App in H. fex H p Hp. fdestr Hp Hp1 Hp2.
  fhave E : (adj_el HG f q g p Hg Hp2). fcases E E1 E2.
  - fleft. exact (app_intro HG f u v p Hp1 E1).
  - fright. frew_in E2 (OP u`[↑] v`[↑] $0) Hp1. exact Hp1.
Qed.

Lemma app_adj_l {G} (HG : incl ZF0base G) f q g u v : G ⊢C Adj f q g -> G ⊢C App f u v -> G ⊢C App g u v.
Proof.
  intros Hg H. unfold App in H. fex H p Hp. fdestr Hp Hp1 Hp2.
  apply (app_intro HG g u v p Hp1). exact (adj_in_l HG f q g p Hg Hp2).
Qed.

Lemma app_adj_r {G} (HG : incl ZF0base G) f q g u v : G ⊢C Adj f q g -> G ⊢C OP u v q -> G ⊢C App g u v.
Proof. intros Hg H. apply (app_intro HG g u v q H). exact (adj_in_r HG f q g Hg). Qed.

Lemma app_sing {G} (HG : incl ZF0base G) q f u v : G ⊢C Sing q f -> G ⊢C App f u v -> G ⊢C OP u v q.
Proof.
  intros Hf H. unfold App in H. fex H p Hp. fdestr Hp Hp1 Hp2.
  fhave E : (sing_el HG q f p Hf Hp2). frew_in E (OP u`[↑] v`[↑] $0) Hp1. exact Hp1.
Qed.

Lemma app_sing_intro {G} (HG : incl ZF0base G) q f u v : G ⊢C Sing q f -> G ⊢C OP u v q -> G ⊢C App f u v.
Proof. intros Hf H. apply (app_intro HG f u v q H). exact (sing_in HG q f Hf). Qed.
