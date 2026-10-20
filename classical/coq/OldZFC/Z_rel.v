(** * Z_rel: relativization infrastructure for the minimal signature.

    - [relS Y phi]: relativization of [phi] to a SET (term) [Y]: every quantifier bounded by [Y].
    - [D0]: syntactic Delta_0 formulas (quantifiers bounded by a free variable); [Sg]: Sigma
      formulas (Delta_0 closed under ∧, ∨, bounded ∀, unbounded ∃).
    - [D0_abs]: Delta_0 formulas are absolute for every transitive class [M] (Rel.v's [rel]).
    - [Sg_up]: Sigma formulas are upward absolute.
    - [rel_ft]: relativizing a closed universal closure, keeping the M-hypotheses.
    - [transfer]: a ZF-derivation of a closed formula relativizes to [M].  *)
From Coq Require Import Arith Lia List Bool.
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase.
From OldRegCon Require Import Rel.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

(** ** Propositional helpers *)
Section Iff.
Context (G : list form).

Lemma iff_refl' (a : form) : G ⊢C a ↔ a.
Proof. apply CI; apply imp_refl. Qed.

Lemma iff_sym' (a b : form) : G ⊢C a ↔ b -> G ⊢C b ↔ a.
Proof. intros H. apply CI; [exact (CE2 H) | exact (CE1 H)]. Qed.

Lemma iff_trans' (a b c : form) : G ⊢C a ↔ b -> G ⊢C b ↔ c -> G ⊢C a ↔ c.
Proof. intros H1 H2. apply CI; eapply imp_trans; [exact (CE1 H1)|exact (CE1 H2)|exact (CE2 H2)|exact (CE2 H1)]. Qed.

End Iff.

Lemma iff_bin (G : list form) b (a a' c c' : form) :
  G ⊢C a ↔ a' -> G ⊢C c ↔ c' -> G ⊢C bin b a c ↔ bin b a' c'.
Proof.
  intros Ha Hc. destruct b; cbn.
  - apply CI; apply II.
    + apply CI; [eapply IE; [apply weak_cons, (CE1 Ha)|eapply CE1, Ctx; now left]
                |eapply IE; [apply weak_cons, (CE1 Hc)|eapply CE2, Ctx; now left]].
    + apply CI; [eapply IE; [apply weak_cons, (CE2 Ha)|eapply CE1, Ctx; now left]
                |eapply IE; [apply weak_cons, (CE2 Hc)|eapply CE2, Ctx; now left]].
  - apply CI; apply II; (eapply DE; [apply Ctx; now left| |]).
    + apply DI1. eapply IE; [apply weak_cons, weak_cons, (CE1 Ha)|apply Ctx; now left].
    + apply DI2. eapply IE; [apply weak_cons, weak_cons, (CE1 Hc)|apply Ctx; now left].
    + apply DI1. eapply IE; [apply weak_cons, weak_cons, (CE2 Ha)|apply Ctx; now left].
    + apply DI2. eapply IE; [apply weak_cons, weak_cons, (CE2 Hc)|apply Ctx; now left].
  - apply CI; apply II; apply II.
    + eapply IE; [apply weak_cons, weak_cons, (CE1 Hc)|]. eapply IE; [apply Ctx; right; now left|].
      eapply IE; [apply weak_cons, weak_cons, (CE2 Ha)|apply Ctx; now left].
    + eapply IE; [apply weak_cons, weak_cons, (CE2 Hc)|]. eapply IE; [apply Ctx; right; now left|].
      eapply IE; [apply weak_cons, weak_cons, (CE1 Ha)|apply Ctx; now left].
Qed.

(** ** Relativization to a set *)
Fixpoint relS {ff} (Y : term) (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) : form :=
  match phi with
  | falsity => falsity
  | atom P v => @atom _ _ _ falsity_on P v
  | bin b a c => bin b (relS Y a) (relS Y c)
  | quant All a => ∀ ($0 ∈' Y`[↑] → relS Y`[↑] a)
  | quant Ex a => ∃ ($0 ∈' Y`[↑] ∧ relS Y`[↑] a)
  end.

Lemma relS_subst {ff} (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) : forall Y sg,
  (relS Y phi)[sg] = relS Y`[sg] (phi[sg]).
Proof.
  induction phi as [|ff P v|ff b a IHa c IHc|ff q a IHa]; intros Y sg; cbn; try reflexivity.
  - now rewrite IHa, IHc.
  - destruct q; cbn; rewrite IHa; now rewrite up_term.
Qed.

(** ** Delta_0 and Sigma formulas *)
Inductive D0 : form -> Prop :=
  | D0_fal : D0 falsity
  | D0_atom P v : D0 (@atom _ _ _ falsity_on P v)
  | D0_bin b phi psi : D0 phi -> D0 psi -> D0 (bin b phi psi)
  | D0_all k phi : D0 phi -> D0 (∀ ($0 ∈' $(S k) → phi))
  | D0_ex k phi : D0 phi -> D0 (∃ ($0 ∈' $(S k) ∧ phi)).

Inductive Sg : form -> Prop :=
  | Sg_D0 phi : D0 phi -> Sg phi
  | Sg_and phi psi : Sg phi -> Sg psi -> Sg (phi ∧ psi)
  | Sg_or phi psi : Sg phi -> Sg psi -> Sg (phi ∨ psi)
  | Sg_all k phi : Sg phi -> Sg (∀ ($0 ∈' $(S k) → phi))
  | Sg_imp phi psi : D0 phi -> Sg psi -> Sg (phi → psi)
  | Sg_ex phi : Sg phi -> Sg (∃ phi).

(** transitivity of a class [M] (a formula in [$0]) *)
Definition TransC (M : form) : form := ∀ (M → ∀ ($0 ∈' $1 → M)).
#[global] Arguments TransC : simpl never.

(** the fact tactics of Std_setnd also weaken hypotheses [forall k, G ⊢C _] *)
Ltac weaken_facts a G ::=
  repeat match goal with
  | H : G ⊢C _ |- _ => apply (weak_cons G a) in H
  | H : forall k : nat, @prv _ _ _ class G (@?P k) |- _ =>
      let H' := fresh in pose proof (fun k => weak_cons G a _ (H k)) as H'; clear H; rename H' into H
  | H : incl _ G |- _ => apply (incl_cons_r _ G a) in H
  | H : In _ G |- _ => apply (in_cons_r _ a G) in H
  end.

Section Abs.
Variable M : form.
Hypothesis HM : bounded 1 M.

Lemma M_up' sg : M[up sg] = M.
Proof. now apply M_up. Qed.

Lemma trans_use G x z : G ⊢C TransC M -> G ⊢C M[x..] -> G ⊢C z ∈' x -> G ⊢C M[z..].
Proof.
  intros HT Hx Hz. unfold TransC in HT. apply (AllE x) in HT. cbn in HT. rewrite ?M_up' in HT.
  apply (IE HT) in Hx. apply (AllE z) in Hx. cbn in Hx. rewrite ?M_up' in Hx.
  rewrite subst_term_shift in Hx. exact (IE Hx Hz).
Qed.

Lemma Hs_cons G sg z : (forall k, G ⊢C M[(sg k)..]) -> G ⊢C M[z..] -> forall k, G ⊢C M[((z .: sg) k)..].
Proof. intros Hs Hz [|k]; cbn; [exact Hz | apply Hs]. Qed.

Theorem D0_abs phi : D0 phi -> forall G sg, G ⊢C TransC M -> (forall k, G ⊢C M[(sg k)..]) ->
  G ⊢C (rel M phi)[sg] ↔ phi[sg].
Proof.
  induction 1 as [| P v | b phi psi _ IH1 _ IH2 | k phi _ IH | k phi _ IH]; intros G sg HT Hs; cbn.
  - apply iff_refl'.
  - apply iff_refl'.
  - apply iff_bin; [apply IH1|apply IH2]; assumption.
  - unfold funcomp. rewrite M_up'. fsplit.
    + fintro H. fall z. fintro Hz. finst H z. rewrite ?subst_term_shift in H.
      fhave HzM : (trans_use _ _ _ HT (Hs k) Hz). fmp H HzM. fmp H Hz.
      exact (iff_l _ _ _ (IH _ (z .: sg) HT (Hs_cons _ _ _ Hs HzM)) H).
    + fintro H. fall z. fintro HzM. fintro Hz. finst H z. rewrite ?subst_term_shift in H. fmp H Hz.
      exact (iff_r _ _ _ (IH _ (z .: sg) HT (Hs_cons _ _ _ Hs HzM)) H).
  - unfold funcomp. rewrite M_up'. fsplit.
    + fintro H. fex H z Hz. fdestr Hz HzM Hz0. fdestr Hz0 Hz1 Hz2. rewrite ?subst_term_shift in Hz1.
      fexists z. rewrite ?subst_term_shift. fsplit; [exact Hz1|].
      exact (iff_l _ _ _ (IH _ (z .: sg) HT (Hs_cons _ _ _ Hs HzM)) Hz2).
    + fintro H. fex H z Hz. fdestr Hz Hz1 Hz2. rewrite ?subst_term_shift in Hz1.
      fhave HzM : (trans_use _ _ _ HT (Hs k) Hz1).
      fexists z. rewrite ?subst_term_shift. fsplit; [exact HzM|]. fsplit; [exact Hz1|].
      exact (iff_r _ _ _ (IH _ (z .: sg) HT (Hs_cons _ _ _ Hs HzM)) Hz2).
Qed.

End Abs.

Section Abs2.
Variable M : form.
Hypothesis HM : bounded 1 M.

Theorem Sg_up phi : Sg phi -> forall G sg, G ⊢C TransC M -> (forall k, G ⊢C M[(sg k)..]) ->
  G ⊢C (rel M phi)[sg] -> G ⊢C phi[sg].
Proof.
  induction 1 as [phi H0 | phi psi _ IH1 _ IH2 | phi psi _ IH1 _ IH2 | k phi _ IH | phi psi H0 _ IH | phi _ IH];
    intros G sg HT Hs H; cbn in H |- *.
  - exact (iff_l _ _ _ (D0_abs M HM phi H0 G sg HT Hs) H).
  - fsplit; [apply IH1|apply IH2]; auto; [exact (CE1 H)|exact (CE2 H)].
  - fcases H H1 H2; [fleft; now apply IH1|fright; now apply IH2].
  - unfold funcomp in *. rewrite ?(M_up' M HM) in H.
    fall z. fintro Hz. finst H z. rewrite ?subst_term_shift in H.
    fhave HzM : (trans_use M HM _ _ _ HT (Hs k) Hz). fmp H HzM. fmp H Hz.
    exact (IH _ (z .: sg) HT (Hs_cons M _ _ _ Hs HzM) H).
  - fintro Hphi. apply IH; [exact HT|exact Hs|]. fapply H.
    exact (iff_r _ _ _ (D0_abs M HM phi H0 _ sg HT Hs) Hphi).
  - rewrite ?(M_up' M HM) in H. fex H z Hz. fdestr Hz HzM Hz2.
    fexists z. exact (IH _ (z .: sg) HT (Hs_cons M _ _ _ Hs HzM) Hz2).
Qed.

(** relativizing a universal closure, keeping the M-hypotheses of the closure variables *)
Lemma rel_ft n theta : forall G sg,
  (forall G' tau, incl G G' -> (forall k, k < n -> G' ⊢C M[(tau k)..]) -> (forall k, tau (n + k) = sg k) ->
     G' ⊢C (rel M theta)[tau]) ->
  G ⊢C (rel M (forall_times n theta))[sg].
Proof.
  induction n as [|n IH]; intros G sg H.
  - apply H; [intros a Ha; exact Ha | intros k Hk; lia | reflexivity].
  - change (forall_times (S n) theta) with (∀ forall_times n theta). cbn. rewrite ?(M_up' M HM).
    apply AllI_named. intros t. cbn. rewrite ?(M_up' M HM). apply II. rewrite up_inst_form.
    apply IH. intros G' tau HG' Htau Htau'. apply H.
    + intros a Ha. apply HG'. now right.
    + intros k Hk. destruct (Nat.eq_dec k n) as [->|Hne].
      * rewrite <- (Nat.add_0_r n), Htau'. cbn. apply Ctx, HG'. now left.
      * apply Htau. lia.
    + intros k. replace (S n + k) with (n + S k) by lia. now rewrite Htau'.
Qed.

End Abs2.

(** ** Closedness: [fb] and the library's [bounded] *)
Lemma fb_bounded {ff} (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) : forall N, fb N phi -> bounded N phi.
Proof.
  induction phi as [|ff P v|ff b a IHa c IHc|ff q a IHa]; intros N H; cbn in H.
  - constructor.
  - constructor. destruct P; cbn in v, H |- *; rewrite (vec2 v) in H |- *; cbn in H;
      destruct (Vector.hd v) as [n|[]]; destruct (Vector.hd (Vector.tl v)) as [m|[]]; cbn in H.
    all: intros t Ht; apply vec_cons_inv in Ht; destruct Ht as [->|Ht]; [apply bounded_var; lia|].
    all: apply vec_cons_inv in Ht; destruct Ht as [->|Ht]; [apply bounded_var; lia|inversion Ht].
  - constructor; [apply IHa|apply IHc]; tauto.
  - constructor. now apply IHa.
Qed.

(** ** Transfer: ZF-theorems hold relativized to [M] *)
Section Transfer.
Variable M : form.
Hypothesis HM : bounded 1 M.

Theorem transfer (A : list form) (T : form) G x :
  A ⊢C T -> closedf T -> (forall a, In a A -> closedf a) ->
  (forall a, In a A -> G ⊢C rel M a) -> G ⊢C M[x..] -> G ⊢C rel M T.
Proof.
  intros H HT HAc HA Hx.
  assert (Hc : forall phi sg, closedf phi -> (rel M phi)[sg] = rel M phi).
  { intros phi sg Hphi. apply (rel_closed HM). now apply fb_bounded. }
  rewrite <- (Hc T (fun _ => x) HT).
  refine (@rel_prv _ _ M HM class nil _ _ A T H G (fun _ => x) _ _ _).
  - intros b sg [].
  - intros Gamma f. destruct f.
  - intros b [].
  - intros k. exact Hx.
  - intros a Ha. rewrite (Hc a _ (HAc a Ha)). now apply HA.
Qed.

End Transfer.

(** proving [D0] / [Sg] for concrete formulas *)
Ltac d0solve := cbn; repeat (first [ apply D0_fal | apply D0_atom | apply D0_bin | apply D0_all | apply D0_ex ]).
Ltac sgsolve := cbn;
  first [ apply Sg_D0; solve [d0solve]
        | apply Sg_and; sgsolve
        | apply Sg_or; sgsolve
        | apply Sg_all; sgsolve
        | apply Sg_imp; [solve [d0solve]|sgsolve]
        | apply Sg_ex; sgsolve ].

(** a boolean version of [fb] for fast closedness checks by computation *)
Fixpoint fbb {ff} (N : nat) (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) : bool :=
  match phi with
  | falsity => true
  | atom P v =>
      match P return Vector.t term (ar_preds P) -> bool with
      | elem => fun v => Nat.ltb (idx (Vector.hd v)) N && Nat.ltb (idx (Vector.hd (Vector.tl v))) N
      | equal => fun v => Nat.ltb (idx (Vector.hd v)) N && Nat.ltb (idx (Vector.hd (Vector.tl v))) N
      end v
  | bin _ a b => fbb N a && fbb N b
  | quant _ a => fbb (S N) a
  end.

Lemma fbb_fb {ff} (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) : forall N, fbb N phi = true -> fb N phi.
Proof.
  induction phi as [|ff P v|ff b a IHa c IHc|ff q a IHa]; intros N H; cbn in *.
  - exact I.
  - destruct P; apply andb_prop in H as [H1 H2]; apply Nat.ltb_lt in H1, H2; now split.
  - apply andb_prop in H as [H1 H2]. split; auto.
  - auto.
Qed.
Ltac fbcomp := apply fbb_fb; vm_compute; reflexivity.

(** boolean checkers for [D0] / [Sg] (fast, by computation) *)
Definition bnd_atom {ff} (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) : bool :=
  match phi with
  | atom P v =>
      match P return Vector.t term (ar_preds P) -> bool with
      | elem => fun v => match Vector.hd v, Vector.hd (Vector.tl v) with
                         | var 0, var (S _) => true
                         | _, _ => false
                         end
      | equal => fun _ => false
      end v
  | _ => false
  end.

Lemma bnd_atom_sound (phi : form) : bnd_atom phi = true -> exists k, phi = $0 ∈' $(S k).
Proof.
  induction phi as [| P v | b a IHa c IHc | q a IHa] using form_ind_falsity; cbn; try discriminate.
  destruct P; cbn in v |- *; [|discriminate].
  rewrite (vec2 v). cbn. destruct (Vector.hd v) as [[|n]|[]]; [|discriminate].
  destruct (Vector.hd (Vector.tl v)) as [[|k]|[]]; [discriminate|]. intros _. now exists k.
Qed.

Fixpoint isD0 {ff} (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) : bool :=
  match phi with
  | falsity => true
  | atom _ _ => true
  | bin _ a c => isD0 a && isD0 c
  | quant All (bin Impl g a) => bnd_atom g && isD0 a
  | quant Ex (bin Conj g a) => bnd_atom g && isD0 a
  | _ => false
  end.

Ltac inj_ex := repeat match goal with H : existT _ _ _ = existT _ _ _ |- _ =>
  apply Eqdep_dec.inj_pair2_eq_dec in H; [subst | decide equality] end.

Lemma D0_bin_inv b a c : D0 (bin b a c) -> D0 c.
Proof. intros H. inversion H; subst. inj_ex. assumption. Qed.

Lemma isD0_all_inv (a : form) : isD0 (∀ a) = true -> exists k a', a = ($0 ∈' $(S k) → a') /\ isD0 a' = true.
Proof.
  induction a as [| P v | b g IHg a' IHa' | q a' IHa'] using form_ind_falsity; cbn; try discriminate.
  destruct b; try discriminate. intros H. apply andb_prop in H as [H1 H2].
  apply bnd_atom_sound in H1 as [k ->]. now exists k, a'.
Qed.
Lemma isD0_ex_inv (a : form) : isD0 (∃ a) = true -> exists k a', a = ($0 ∈' $(S k) ∧ a') /\ isD0 a' = true.
Proof.
  induction a as [| P v | b g IHg a' IHa' | q a' IHa'] using form_ind_falsity; cbn; try discriminate.
  destruct b; try discriminate. intros H. apply andb_prop in H as [H1 H2].
  apply bnd_atom_sound in H1 as [k ->]. now exists k, a'.
Qed.

Lemma isD0_sound (phi : form) : isD0 phi = true -> D0 phi.
Proof.
  induction phi as [| P v | b a IHa c IHc | q a IHa] using form_ind_falsity; intros H.
  - constructor.
  - constructor.
  - cbn in H. apply andb_prop in H as [H1 H2]. constructor; auto.
  - destruct q.
    + apply isD0_all_inv in H as (k & a' & -> & H). constructor.
      apply (D0_bin_inv Impl ($0 ∈' $(S k))). apply IHa. cbn. now rewrite H.
    + apply isD0_ex_inv in H as (k & a' & -> & H). constructor.
      apply (D0_bin_inv Conj ($0 ∈' $(S k))). apply IHa. cbn. now rewrite H.
Qed.

Fixpoint isSg {ff} (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) : bool :=
  isD0 phi ||
  match phi with
  | bin Conj a c => isSg a && isSg c
  | bin Disj a c => isSg a && isSg c
  | bin Impl a c => isD0 a && isSg c
  | quant All (bin Impl g a) => bnd_atom g && isSg a
  | quant Ex a => isSg a
  | _ => false
  end.

Lemma Sg_imp_inv g a : Sg (g → a) -> Sg a.
Proof.
  intros H. inversion H; subst.
  - apply Sg_D0. now apply (D0_bin_inv Impl g a).
  - inj_ex. assumption.
Qed.

Lemma isSg_all_inv (a : form) : isSg (∀ a) = true -> isD0 (∀ a) = true \/
  exists k a', a = ($0 ∈' $(S k) → a') /\ isSg a' = true.
Proof.
  intros H. cbn in H. apply orb_prop in H as [H|H]; [now left|right]. revert H.
  induction a as [| P v | b g IHg a' IHa' | q a' IHa'] using form_ind_falsity; cbn; try discriminate.
  destruct b; try discriminate. intros H. apply andb_prop in H as [H1 H2].
  apply bnd_atom_sound in H1 as [k ->]. now exists k, a'.
Qed.

Lemma isSg_sound (phi : form) : isSg phi = true -> Sg phi.
Proof.
  induction phi as [| P v | b a IHa c IHc | q a IHa] using form_ind_falsity; intros H.
  - apply Sg_D0. constructor.
  - apply Sg_D0. constructor.
  - cbn in H. apply orb_prop in H as [H|H]; [apply Sg_D0, isD0_sound; exact H|].
    destruct b; apply andb_prop in H as [H1 H2].
    + apply Sg_and; auto.
    + apply Sg_or; auto.
    + apply Sg_imp; [now apply isD0_sound | auto].
  - destruct q.
    + apply isSg_all_inv in H as [H|(k & a' & -> & H)]; [apply Sg_D0, isD0_sound; exact H|].
      apply Sg_all. apply (Sg_imp_inv ($0 ∈' $(S k))). apply IHa. cbn. rewrite H. now rewrite orb_true_r.
    + cbn in H. apply orb_prop in H as [H|H]; [apply Sg_D0, isD0_sound; exact H|]. apply Sg_ex. auto.
Qed.

Ltac d0comp := apply isD0_sound; vm_compute; reflexivity.
Ltac sgcomp := apply isSg_sound; vm_compute; reflexivity.
