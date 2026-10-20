(** * Z_axL: every axiom of ZF + regularity holds relativized to L. *)
From Coq Require Import Arith Lia List.
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_setinf.
From OldRegCon Require Import Rel.
From OldZFC Require Import Z_rel Z_base Z_prim Z_ord Z_trec Z_cl Z_L Z_refl.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.


(** ** Infrastructure *)
#[local] Arguments Lform : simpl never.
#[local] Arguments InL : simpl never.

Lemma Lform_up sg : Lform[up sg] = Lform.
Proof. exact (M_up' Lform bounded_Lform sg). Qed.
Lemma Lform_inst t : Lform[t..] = InL t.
Proof. reflexivity. Qed.
Lemma InL_subst t sg : (InL t)[sg] = InL t`[sg].
Proof. unfold InL. apply (M_subst bounded_Lform). Qed.
Lemma relL_subst (phi : form) sg : (rel Lform phi)[sg] = rel Lform (phi[sg]).
Proof. apply (rel_subst bounded_Lform). Qed.
Lemma relS_subst' (phi : form) Y sg : (relS Y phi)[sg] = relS Y`[sg] (phi[sg]).
Proof. apply relS_subst. Qed.
#[local] Hint Rewrite Lform_up Lform_inst InL_subst relL_subst relS_subst' : fsub.

Lemma wk {G G' : list form} {phi : form} : incl G G' -> G ⊢C phi -> G' ⊢C phi.
Proof. intros H1 H2. exact (Weak H2 H1). Qed.

Ltac weaken_facts a G ::=
  repeat match goal with
  | H : G ⊢C _ |- _ => apply (weak_cons G a) in H
  | H : forall k : nat, @prv _ _ _ class G (@?P k) |- _ =>
      let H' := fresh in pose proof (fun k => weak_cons G a _ (H k)) as H'; clear H; rename H' into H
  | H : forall k : nat, k < ?m -> @prv _ _ _ class G (@?P k) |- _ =>
      let H' := fresh in pose proof (fun k hk => weak_cons G a _ (H k hk)) as H'; clear H; rename H' into H
  | H : incl _ G |- _ => apply (incl_cons_r _ G a) in H
  | H : In _ G |- _ => apply (in_cons_r _ a G) in H
  end.

(** move every fact about G to an extension G' *)
Ltac lift HGG' :=
  match type of HGG' with incl ?G ?G' =>
  repeat match goal with
  | H : G ⊢C _ |- _ => apply (wk HGG') in H
  | H : forall k : nat, k < ?m -> @prv _ _ _ class G (@?P k) |- _ =>
      let H' := fresh in pose proof (fun k hk => wk HGG' (H k hk)) as H'; clear H; rename H' into H
  | H : incl ?L G |- _ => apply (fun h => incl_tran h HGG') in H
  | H : In _ G |- _ => apply HGG' in H
  end end; clear HGG'.

(** ∃-elimination without simplification of the new fact *)
Ltac fex_raw H x Hx := apply (ExE_named H); intros x; ctx_push Hx; try clear H.

Lemma sub0_use {G} x y z : G ⊢C Sub0 x y -> G ⊢C z ∈' x -> G ⊢C z ∈' y.
Proof. intros H Hz. unfold Sub0 in H. finst H z. exact (IE H Hz). Qed.

Lemma sub0_intro {G} x y : (forall G' z, incl G G' -> G' ⊢C z ∈' x -> G' ⊢C z ∈' y) -> G ⊢C Sub0 x y.
Proof.
  intros H. unfold Sub0. apply AllI_named. intros z. simp. apply II.
  apply H; [intros a Ha; now right | apply Ctx; now left].
Qed.

Lemma sub0_refl {G} x : G ⊢C Sub0 x x.
Proof. apply sub0_intro. intros G' z _ Hz. exact Hz. Qed.

Lemma sub0_trans {G} x y w : G ⊢C Sub0 x y -> G ⊢C Sub0 y w -> G ⊢C Sub0 x w.
Proof.
  intros H1 H2. apply sub0_intro. intros G' z HG' Hz. lift HG'.
  eapply sub0_use; [exact H2|]. eapply sub0_use; [exact H1|exact Hz].
Qed.

Lemma trans0_use {G} x y z : G ⊢C Trans0 x -> G ⊢C y ∈' x -> G ⊢C z ∈' y -> G ⊢C z ∈' x.
Proof. intros H Hy Hz. unfold Trans0 in H. finst H y. fmp H Hy. finst H z. exact (IE H Hz). Qed.

Section Basic.
Context {G : list form} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G).

Lemma inL_el x z : G ⊢C InL x -> G ⊢C z ∈' x -> G ⊢C InL z.
Proof.
  intros Hx Hz. assert (HT : G ⊢C TransC Lform) by (eapply L_transC; eassumption).
  exact (trans_use Lform bounded_Lform G x z HT Hx Hz).
Qed.

End Basic.

(** ** Relativized library predicates *)
Lemma rel_sub' x y : rel Lform (sub' x y) = ∀ (Lform → $0 ∈' x`[↑] → $0 ∈' y`[↑]).
Proof. reflexivity. Qed.
Lemma rel_is_eset x : rel Lform (is_eset x) = ∀ (Lform → ¬ ($0 ∈' x`[↑])).
Proof. reflexivity. Qed.
Lemma rel_is_pair x y p : rel Lform (is_pair x y p) = ∀ (Lform → ($0 ∈' p`[↑] ↔ $0 ≡' x`[↑] ∨ $0 ≡' y`[↑])).
Proof. reflexivity. Qed.
Lemma rel_is_union x u : rel Lform (is_union x u) =
  ∀ (Lform → ($0 ∈' u`[↑] ↔ ∃ (Lform ∧ ($0 ∈' x`[↑]`[↑] ∧ $1 ∈' $0)))).
Proof. reflexivity. Qed.
Lemma rel_is_power x p : rel Lform (is_power x p) = ∀ (Lform → ($0 ∈' p`[↑] ↔ rel Lform (sub' $0 x`[↑]))).
Proof. reflexivity. Qed.
Lemma rel_is_sigma x s : rel Lform (is_sigma x s) = ∀ (Lform → ($0 ∈' s`[↑] ↔ $0 ∈' x`[↑] ∨ $0 ≡' x`[↑])).
Proof. reflexivity. Qed.

Section L1.
Context {G : list form} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G).

Lemma subL_sub x y : G ⊢C InL x -> G ⊢C rel Lform (sub' x y) -> G ⊢C sub' x y.
Proof using HG HR HOm HL.
  intros Hx H. rewrite rel_sub' in H. unfold sub'. fall z. fintro Hz.
  fassert HzL : (InL z). { eapply inL_el; eassumption. }
  finst H z. fmp H HzL. exact (IE H Hz).
Qed.

Lemma sub_subL x y : G ⊢C sub' x y -> G ⊢C rel Lform (sub' x y).
Proof using HG HR HOm HL.
  intros H. rewrite rel_sub'. unfold sub' in H. fall z. fintro Hd. fintro Hz. finst H z. exact (IE H Hz).
Qed.

(** finitely many elements of L lie in one level above a given ordinal *)
Lemma L_common m sg a psi : (forall k, k < m -> G ⊢C InL (sg k)) -> G ⊢C Ord0 a ->
  (forall G' b Y, incl G G' -> G' ⊢C Ord0 b -> G' ⊢C Sub0 a b -> G' ⊢C LL b Y ->
     (forall k, k < m -> G' ⊢C sg k ∈' Y) -> G' ⊢C psi) -> G ⊢C psi.
Proof using HG HR HOm HL.
  revert psi. induction m as [|m IH]; intros psi Hs Ha K.
  - assert (H : G ⊢C ∃ LL a`[↑] $0) by (eapply LL_ex; eassumption).
    apply (ExE_named H). intros Y.
    assert (E : (LL a`[↑] $0)[Y..] = LL a Y) by (simp; reflexivity). rewrite E.
    apply K with (b := a) (Y := Y).
    + intros c Hc. now right.
    + now apply weak_cons.
    + apply sub0_refl.
    + apply Ctx. now left.
    + intros k Hk. lia.
  - apply IH; [intros k Hk; apply Hs; lia | exact Ha |].
    intros G' b Y HGG' Hb Hab HY Hin.
    pose proof (incl_tran HG HGG') as HG'. pose proof (HGG' _ HR) as HR'. pose proof (HGG' _ HOm) as HOm'.
    pose proof (incl_tran HL HGG') as HL'.
    assert (Hm : G' ⊢C InL (sg m)) by (apply (wk HGG'), Hs; lia).
    assert (H : G' ⊢C ∃ (∃ (Ord0 $1 ∧ Sub0 b`[↑]`[↑] $1 ∧ LL $1 $0 ∧ (sg m)`[↑]`[↑] ∈' $0)))
      by (eapply L_above; eassumption).
    apply (ExE_named H). intros b'. eapply ExE_named; [apply Ctx; now left|]. intros Y'.
    match goal with |- @prv _ _ _ _ ?GG _ => set (G'' := GG) end.
    assert (HG'' : incl G' G'') by (intros c Hc; right; now right).
    assert (H'' : G'' ⊢C (Ord0 $1 ∧ Sub0 b`[↑]`[↑] $1 ∧ LL $1 $0 ∧ (sg m)`[↑]`[↑] ∈' $0)[up (b'..)][Y'..])
      by (apply Ctx; now left).
    clearbody G''. simp_in H''. lift HG''.
    fdestr H'' H13 H4. fdestr H13 H12 H3. fdestr H12 H1 H2.
    apply K with (b := b') (Y := Y').
    + exact HGG'.
    + exact H1.
    + eapply sub0_trans; eassumption.
    + exact H3.
    + intros k Hk. destruct (Nat.eq_dec k m) as [->|Hne]; [exact H4|].
      eapply sub0_use; [|apply Hin; lia]. eapply LL_sub with (a := b') (b := b); eassumption.
Qed.

(** definable subsets of a level are in L *)
Lemma L_definable m phi sg b Y : fb (S m) phi -> G ⊢C Ord0 b -> G ⊢C LL b Y ->
  (forall k, k < m -> G ⊢C sg k ∈' Y) ->
  G ⊢C ∃ (InL $0 ∧ ∀ ($0 ∈' $1 ↔ $0 ∈' Y`[↑]`[↑] ∧ relS Y`[↑]`[↑] (phi[up (sg >> subst_term ↑)]))).
Proof using HG HR HOm HL.
  intros Hphi Hb HY Hs. pose proof (Ax_L_cl _ HL) as HC.
  assert (HD : G ⊢C ∃ Def0 Y`[↑] $0) by (eapply def_ex; eassumption).
  apply (ExE_named HD). intros D.
  assert (HDY : ((Def0 Y`[↑] $0)[D..] :: G) ⊢C Def0 Y D) by (apply Ctx; left; simp; reflexivity).
  assert (H1 : incl G ((Def0 Y`[↑] $0)[D..] :: G)) by (intros c Hc; now right).
  set (G1 := (Def0 Y`[↑] $0)[D..] :: G) in *. clearbody G1. lift H1.
  assert (Hdef : G1 ⊢C ∃ ($0 ∈' D`[↑] ∧ ∀ ($0 ∈' $1 ↔ $0 ∈' Y`[↑]`[↑] ∧ relS Y`[↑]`[↑] (phi[up (sg >> subst_term ↑)]))))
    by (eapply definable; eassumption).
  apply (ExE_named Hdef). intros X. apply (ExI X).
  assert (H : (($0 ∈' D`[↑] ∧ ∀ ($0 ∈' $1 ↔ $0 ∈' Y`[↑]`[↑] ∧ relS Y`[↑]`[↑] (phi[up (sg >> subst_term ↑)])))[X..]
              :: G1) ⊢C
              ($0 ∈' D`[↑] ∧ ∀ ($0 ∈' $1 ↔ $0 ∈' Y`[↑]`[↑] ∧ relS Y`[↑]`[↑] (phi[up (sg >> subst_term ↑)])))[X..])
    by (apply Ctx; now left).
  apply CI; [|exact (CE2 H)].
  pose proof (CE1 H) as H2. simp_in H2. simp.
  eapply L_def with (a := b) (Y := Y) (D := D); try (apply weak_cons; eassumption); try (intros c Hc; right; auto; fail);
    try (right; auto; fail); exact H2.
Qed.

End L1.

Lemma def_mem {G} (phi : form) sg Y X z :
  G ⊢C (∀ ($0 ∈' $1 ↔ $0 ∈' Y`[↑]`[↑] ∧ relS Y`[↑]`[↑] (phi[up (sg >> subst_term ↑)])))[X..] ->
  G ⊢C z ∈' X ↔ z ∈' Y ∧ relS Y (phi[z .: sg]).
Proof.
  intros H. apply (AllE z) in H. cbn in H. rewrite ?subst_term_shift, ?relS_subst in H. cbn in H.
  rewrite ?subst_term_shift in H.
  assert (EY : Y`[↑]`[↑]`[up (X..)]`[z..] = Y) by (rewrite !subst_term_comp; apply subst_term_id; reflexivity).
  rewrite ?EY in H.
  match type of H with context [relS _ ?p] => replace p with (phi[z .: sg]) in H; [exact H|] end.
  rewrite !subst_comp. apply subst_ext. intros [|k]; cbn; [reflexivity|].
  unfold funcomp. rewrite !subst_term_comp. symmetry. apply subst_term_id. intros n. reflexivity.
Qed.

(** ** The finitely many axioms *)
Section AxBase.
Context {G : list form} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G).

Lemma axL_refl : G ⊢C rel Lform ax_refl'.
Proof using HG HR HOm HL.
  unfold ax_refl'. cbn. fall x. fintro Hx. apply (eq_refl' HG).
Qed.

Lemma axL_sym : G ⊢C rel Lform ax_sym'.
Proof using HG HR HOm HL.
  unfold ax_sym'. cbn. fall x. fintro Hx. fall y. fintro Hy. fintro H. now apply (eq_sym' HG).
Qed.

Lemma axL_trans : G ⊢C rel Lform ax_trans'.
Proof using HG HR HOm HL.
  unfold ax_trans'. cbn. fall x. fintro Hx. fall y. fintro Hy. fall z. fintro Hz.
  fintro H1. fintro H2. exact (eq_trans' HG _ _ _ H1 H2).
Qed.

Lemma axL_eq_elem : G ⊢C rel Lform ax_eq_elem'.
Proof using HG HR HOm HL.
  unfold ax_eq_elem'. cbn. fall a. fintro Ha. fall b. fintro Hb. fall c. fintro Hc. fall d. fintro Hd.
  fintro H1. fintro H2. fintro H3. exact (elem_cong HG _ _ _ _ H1 H2 H3).
Qed.

Lemma axL_ext : G ⊢C rel Lform ax_ext'.
Proof using HG HR HOm HL.
  unfold ax_ext'. cbn. fall x. fintro Hx. fall y. fintro Hy. fintro H1. fintro H2.
  apply (ext_rule HG); eapply subL_sub; eassumption.
Qed.

Lemma axL_eset : G ⊢C rel Lform ax_eset'.
Proof using HG HR HOm HL.
  pose proof (Ax_cl_ord _ (Ax_L_cl _ HL)) as HO. pose proof (Ax_ord_prim _ HO) as HP.
  unfold ax_eset'. cbn.
  assert (He : G ⊢C ∃ Emp0 $0) by (eapply emp0_ex; eassumption). fex He e He0.
  fexists e. fsplit.
  - fassert Ho : (Ord0 e). { eapply ord_emp; eassumption. }
    eapply L_ord; eassumption.
  - rewrite rel_is_eset. fall z. fintro Hz. fintro Hze. unfold Emp0 in He0. finst He0 z. exact (IE He0 Hze).
Qed.

Lemma axL_reg0 : G ⊢C rel Lform ax_reg'.
Proof using HG HR HOm HL.
  assert (Hreg : G ⊢C ax_reg') by (apply Ctx; exact HR).
  unfold MinZF.ax_reg' in *. cbn. fall x. fintro Hx. fintro Hne.
  finst Hreg x.
  fassert Hne' : (∃ $0 ∈' x`[↑]). { fex Hne y Hy. fdestr Hy Hy1 Hy2. fexists y. exact Hy2. }
  fmp Hreg Hne'. fex Hreg m Hm. fdestr Hm Hm1 Hm2. fexists m. fsplit; [|fsplit].
  - eapply inL_el; eassumption.
  - exact Hm1.
  - fall z. fintro Hz. fintro Hzm. finst Hm2 z. fmp Hm2 Hzm. exact Hm2.
Qed.

Lemma axL_pair : G ⊢C rel Lform ax_pair'.
Proof using HG HR HOm HL.
  pose proof (Ax_cl_ord _ (Ax_L_cl _ HL)) as HO. pose proof (Ax_ord_prim _ HO) as HP.
  unfold ax_pair'. cbn. fall x. fintro Hx. fall y. fintro Hy.
  fassert He : (∃ Emp0 $0). { eapply emp0_ex; eassumption. } fex He e He0.
  fassert Ho : (Ord0 e). { eapply ord_emp; eassumption. }
  apply (L_common HG HR HOm HL 2 (x .: y .: var) e); [intros [|[|k]] Hk; cbn; [exact Hx|exact Hy|lia] | exact Ho |].
  intros G' b Y HGG' Hb _ HY Hin. lift HGG'.
  pose proof (L_definable HG HR HOm HL 2 ($0 ≡' $1 ∨ $0 ≡' $2) (x .: y .: var) b Y ltac:(fbcomp) Hb HY Hin) as HX.
  fex_raw HX X HX0. fdestr HX0 HXL HXd. simp_in HXL.
  fexists X. fsplit; [exact HXL|]. rewrite rel_is_pair. fall z. fintro Hz.
  pose proof (def_mem ($0 ≡' $1 ∨ $0 ≡' $2) (x .: y .: var) Y X z HXd) as Hm. cbn in Hm.
  fsplit.
  - fintro H. exact (CE2 (iff_l _ _ _ Hm H)).
  - fintro H. apply (iff_r _ _ _ Hm). fsplit; [|exact H].
    fcases H H1 H2.
    + apply (elem_cong HG x Y z Y); [now apply (eq_sym' HG) | apply (eq_refl' HG) | apply (Hin 0); lia].
    + apply (elem_cong HG y Y z Y); [now apply (eq_sym' HG) | apply (eq_refl' HG) | apply (Hin 1); lia].
Qed.

Lemma axL_union : G ⊢C rel Lform ax_union'.
Proof using HG HR HOm HL.
  pose proof (Ax_cl_ord _ (Ax_L_cl _ HL)) as HO. pose proof (Ax_ord_prim _ HO) as HP.
  unfold ax_union'. cbn. fall x. fintro Hx.
  fassert He : (∃ Emp0 $0). { eapply emp0_ex; eassumption. } fex He e He0.
  fassert Ho : (Ord0 e). { eapply ord_emp; eassumption. }
  apply (L_common HG HR HOm HL 1 (x .: var) e); [intros [|k] Hk; cbn; [exact Hx|lia] | exact Ho |].
  intros G' b Y HGG' Hb _ HY Hin. lift HGG'.
  assert (HxY : G' ⊢C x ∈' Y) by (apply (Hin 0); lia).
  assert (HT : G' ⊢C Trans0 Y) by (eapply LL_trans; eassumption).
  pose proof (L_definable HG HR HOm HL 1 (∃ ($0 ∈' $2 ∧ $1 ∈' $0)) (x .: var) b Y ltac:(fbcomp) Hb HY Hin) as HX.
  fex_raw HX X HX0. fdestr HX0 HXL HXd. simp_in HXL.
  fexists X. fsplit; [exact HXL|]. rewrite rel_is_union. fall z. fintro Hz.
  pose proof (def_mem (∃ ($0 ∈' $2 ∧ $1 ∈' $0)) (x .: var) Y X z HXd) as Hm. simp_in Hm.
  fsplit.
  - fintro H. pose proof (CE2 (iff_l _ _ _ Hm H)) as H'. fex H' w Hw. fdestr Hw Hw1 Hw2. fdestr Hw2 Hw2a Hw3.
    fexists w. fsplit; [|fsplit; assumption]. eapply inL_el with (x := x); eassumption.
  - fintro H. apply (iff_r _ _ _ Hm). fex H w Hw. fdestr Hw Hw1 Hw2. fdestr Hw2 Hw2a Hw3.
    fassert HwY : (w ∈' Y). { eapply trans0_use with (y := x); eassumption. }
    fsplit; [eapply trans0_use with (y := w); eassumption|].
    fexists w. fsplit; [exact HwY|]. fsplit; assumption.
Qed.

End AxBase.

(** ** Formulas and instance lists *)
(** Q(δ, v): if v ∈ L then v ∈ L_δ ($0 = δ, $1 = v) *)
Definition Qpow : form := InL $1 → ∃ (LL $1 $0 ∧ $2 ∈' $0).
Lemma fb_Qpow : fb 2 Qpow.
Proof. fbcomp. Qed.
#[local] Arguments Qpow : simpl never.
Lemma Qpow_subst s : Qpow[s] = (InL (s 1) → ∃ (LL (s 0)`[↑] $0 ∧ (s 1)`[↑] ∈' $0)).
Proof. unfold Qpow. cbn. rewrite InL_subst. cbn. now rewrite LL_subst. Qed.
#[local] Hint Rewrite Qpow_subst : fsub.

(** collection instance bounding P(x) ∩ L (and images) inside one level *)
Definition powL_insts : list form := oc_insts 0 Qpow.

(** replacement: the V-instance (u, v ∈ L and φ^L(u, v)) and the reflected formula ∃u ∈ x φ(u, v) *)
Definition repF (phi : form) : form := (InL $0 ∧ InL $1) ∧ rel Lform phi.
Definition psiR (phi : form) : form := ∃ ($0 ∈' $2 ∧ phi[$0 .: $1 .: (fun k => $(S (S (S k))))]).
(** separation: the reflected formula z ∈ x ∧ φ(z) is handled by reflecting φ *)
Definition psiS (phi : form) : form := $0 ∈' $1 ∧ phi[$0 .: (fun k => $(S (S k)))].

Lemma idx_shift (t : term) : idx t`[↑] = S (idx t).
Proof. destruct t as [k|[]]. reflexivity. Qed.

Lemma fb_rel (phi : form) : forall N, fb N phi -> fb N (rel Lform phi).
Proof.
  induction phi as [| P v | b a IHa c IHc | q a IHa] using form_ind_falsity; intros N H; cbn in *.
  - exact I.
  - exact H.
  - destruct H. split; auto.
  - destruct q; cbn; (split; [eapply fb_mono; [exact fb_Lform|lia] | now apply IHa]).
Qed.

Lemma fb_repF n phi : fb (S (S n)) phi -> fb (S (S n)) (repF phi).
Proof.
  intros H. unfold repF. cbn. split; [split|].
  - unfold InL. eapply fb_subst; [exact fb_Lform|]. intros [|i] Hi; cbn; lia.
  - unfold InL. eapply fb_subst; [exact fb_Lform|]. intros [|i] Hi; cbn; lia.
  - now apply fb_rel.
Qed.

Lemma fb_psiR n phi : fb (S (S n)) phi -> fb (S (S n)) (psiR phi).
Proof.
  intros H. unfold psiR. cbn. split; [lia|].
  eapply fb_subst; [exact H|]. intros [|[|i]] Hi; cbn; lia.
Qed.

Lemma fb_psiS n phi : fb (S n) phi -> fb (S (S n)) (psiS phi).
Proof.
  intros H. unfold psiS. cbn. split; [lia|].
  eapply fb_subst; [exact H|]. intros [|i] Hi; cbn; lia.
Qed.

(** fb under a renaming that is injective enough *)
Lemma fb_ren_inv (phi : form) : forall N M (sg : nat -> term),
  fb M (phi[sg]) -> (forall i, idx (sg i) < M -> i < N) -> fb N phi.
Proof.
  induction phi as [| P v | b a IHa c IHc | q a IHa] using form_ind_falsity; intros N M sg H Hs; cbn in *.
  - exact I.
  - destruct P; cbn in v, H |- *; rewrite (vec2 v) in H |- *; cbn in *;
      destruct (Vector.hd v) as [i|[]]; destruct (Vector.hd (Vector.tl v)) as [j|[]]; cbn in *;
      destruct H; split; apply Hs; assumption.
  - destruct H. split; [eapply IHa|eapply IHc]; eauto.
  - eapply IHa; [exact H|]. intros [|i] Hi; [lia|]. cbn in Hi. unfold funcomp in Hi.
    rewrite idx_shift in Hi. specialize (Hs i). lia.
Qed.

Lemma fb_sep_inv n phi : closedf (forall_times n (ax_sep' phi)) -> fb (S n) phi.
Proof.
  intros H. apply fb_forall_times in H. rewrite Nat.add_0_r in H. unfold ax_sep' in H. cbn in H.
  destruct H as [[_ [_ H]] _]. eapply fb_ren_inv; [exact H|].
  intros [|i] Hi; cbn in Hi |- *; lia.
Qed.

Lemma fb_rep_inv n phi : closedf (forall_times n (ax_rep' phi)) -> fb (S (S n)) phi.
Proof.
  intros H. apply fb_forall_times in H. rewrite Nat.add_0_r in H. unfold ax_rep', fun_rel' in H. cbn in H.
  destruct H as [[H _] _]. eapply fb_ren_inv; [exact H|].
  intros [|[|i]] Hi; cbn in Hi |- *; lia.
Qed.

(** instances used for separation / replacement of φ *)
Definition sepL_insts (n : nat) (phi : form) : list form := refl_insts (S n) phi.
Definition repL_insts (n : nat) (phi : form) : list form :=
  forall_times n (ax_rep' (repF phi)) :: refl_insts (S (S n)) (psiR phi) ++ powL_insts.
Lemma sepL_insts_ok n phi a : fb (S n) phi -> In a (sepL_insts n phi) -> ZFR a.
Proof. intros H Ha. exact (refl_insts_ok _ _ _ H Ha). Qed.
Lemma repL_insts_ok n phi a : fb (S (S n)) phi -> In a (repL_insts n phi) -> ZFR a.
Proof.
  intros H [<-|Ha]; [now apply ZFR_rep, fb_repF|].
  apply in_app_iff in Ha as [Ha|Ha]; [exact (refl_insts_ok _ _ _ (fb_psiR _ _ H) Ha)|].
  exact (oc_insts_ok 0 Qpow a fb_Qpow Ha).
Qed.

(** ** Reflection: substitution *)
Lemma iter_up_S k (s : nat -> term) : iter up k (up s) = iter up (S k) s.
Proof. induction k as [|k IH]; cbn; [reflexivity|]. cbn in IH. now rewrite IH. Qed.

Lemma iter_up_lt k : forall (s : nat -> term) i, i < k -> iter up k s i = $i.
Proof.
  induction k as [|k IH]; intros s i Hi; [lia|]. cbn. destruct i as [|i]; [reflexivity|].
  cbn. unfold funcomp. rewrite IH by lia. reflexivity.
Qed.

Lemma ballS_subst m : forall Y body sg, (ballS m Y body)[sg] = ballS m Y`[sg] (body[iter up m sg]).
Proof.
  induction m as [|m IH]; intros Y body sg; cbn; [reflexivity|].
  rewrite IH, iter_up_S. cbn. now rewrite up_term.
Qed.

Lemma Refl_subst m phi b sg : fb m phi -> (Refl m phi b)[sg] = Refl m phi b`[sg].
Proof.
  intros H. unfold Refl. cbn. rewrite LL_subst, ballS_subst. cbn.
  rewrite ?up_term, ?relL_subst, ?relS_subst, ?iter_up_S.
  assert (E1 : phi[iter up (S m) sg] = phi).
  { rewrite (subst_ext_fb phi m (iter up (S m) sg) var H) by (intros i Hi; apply iter_up_lt; lia).
    apply subst_var. }
  assert (E2 : $m`[iter up (S m) sg] = $m) by exact (iter_up_lt (S m) sg m ltac:(lia)).
  assert (E3 : iter up (S m) sg m = $m) by (apply iter_up_lt; lia).
  rewrite ?E1, ?E2, ?E3. reflexivity.
Qed.

Ltac fse := rewrite ?subst_comp; apply subst_ext; let k := fresh "k" in intros [|[|[|[|[|[|k]]]]]]; term_eq.
Ltac nphi phi t := rewrite ?(subst_comp phi); try match goal with |- context [phi[?s]] => assert_fails (constr_eq s t); replace (phi[s]) with (phi[t]) by fse end.
Ltac nphi_in H phi t := rewrite ?(subst_comp phi) in H; try match type of H with context [phi[?s]] => assert_fails (constr_eq s t); replace (phi[s]) with (phi[t]) in H by fse end.

Lemma rel_sep_eq phi tau : rel Lform ((ax_sep' phi)[tau]) =
  ∀ (Lform → ∃ (Lform ∧ ∀ (Lform → ($0 ∈' $1 ↔ $0 ∈' $2 ∧ rel Lform (phi[$0 .: (fun k => (tau k)`[↑]`[↑]`[↑])]))))).
Proof. cbn [ax_sep' rel subst_form]. nphi phi ($0 .: (fun k => (tau k)`[↑]`[↑]`[↑])). reflexivity. Qed.

Lemma rel_rep_eq phi tau : rel Lform ((ax_rep' phi)[tau]) =
  ((∀ (Lform → ∀ (Lform → ∀ (Lform → rel Lform (phi[$2 .: $1 .: (fun k => (tau k)`[↑]`[↑]`[↑])]) →
       rel Lform (phi[$2 .: $0 .: (fun k => (tau k)`[↑]`[↑]`[↑])]) → $1 ≡' $0)))) →
   ∀ (Lform → ∃ (Lform ∧ ∀ (Lform → ($0 ∈' $1 ↔
       ∃ (Lform ∧ ($0 ∈' $3 ∧ rel Lform (phi[$0 .: $1 .: (fun k => (tau k)`[↑]`[↑]`[↑]`[↑])])))))))).
Proof.
  cbn [ax_rep' fun_rel' rel subst_form].
  nphi phi ($2 .: $1 .: (fun k => (tau k)`[↑]`[↑]`[↑])).
  nphi phi ($2 .: $0 .: (fun k => (tau k)`[↑]`[↑]`[↑])).
  nphi phi ($0 .: $1 .: (fun k => (tau k)`[↑]`[↑]`[↑]`[↑])).
  reflexivity.
Qed.

Lemma rep_mem {G} phi tau x Z v :
  G ⊢C (∀ ($0 ∈' $1 ↔ ∃ ($0 ∈' x`[↑]`[↑]`[↑] ∧ (repF phi)[$0 .: $1 .: (fun k => (tau k)`[↑]`[↑]`[↑])])))[Z..] ->
  G ⊢C v ∈' Z ↔ ∃ ($0 ∈' x`[↑] ∧ ((InL $0 ∧ InL v`[↑]) ∧ rel Lform (phi[$0 .: v`[↑] .: (fun k => (tau k)`[↑])]))).
Proof.
  intros H. apply (AllE v) in H. unfold repF in H. simp_in H.
  nphi_in H phi ($0 .: v`[↑] .: (fun k => (tau k)`[↑])). exact H.
Qed.

Ltac ctxof := match goal with |- ?GG ⊢C _ => GG end.

Section AxL2.
Context {G : list form} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G).

(** every set X has a level containing X ∩ L *)
Lemma L_bound X : incl powL_insts G ->
  G ⊢C ∃ (∃ (Ord0 $1 ∧ LL $1 $0 ∧ ∀ ($0 ∈' X`[↑]`[↑]`[↑] → InL $0 → $0 ∈' $1))).
Proof using HG HR HOm HL.
  intros Hpw. pose proof (Ax_cl_ord _ (Ax_L_cl _ HL)) as HO. pose proof (Ax_ord_prim _ HO) as HP.
  pose proof fb_Qpow as HQ.
  fassert He : (∃ Emp0 $0). { eapply emp0_ex; eassumption. } fex He e He0.
  fassert Ho : (Ord0 e). { eapply ord_emp; eassumption. }
  fassert H1 : (∀ ($0 ∈' X`[↑] → ∃ (Ord0 $0 ∧ Qpow[up (up var)]))).
  { fall v. fintro Hv. apply (XM_rule _ (InL v)).
    - fintro HvL. pose proof HvL as H'. rewrite InL_eq in H'. fex H' a Ha. fex Ha Y HY.
      fdestr HY HY12 HY3. fdestr HY12 HY1 HY2. fexists a. fsplit; [exact HY1|].
      fintro Hd. fexists Y. fsplit; assumption.
    - fintro HnL. fexists e. fsplit; [exact Ho|]. fintro HvL. fabsurd. exact (IE HnL HvL). }
  fassert H2 : (∀ (∀ (∀ (Ord0 $1 → Ord0 $0 → Sub0 $1 $0 →
                Qpow[$1 .: $2 .: (fun k => (var k)`[↑]`[↑]`[↑])] → Qpow[$0 .: $2 .: (fun k => (var k)`[↑]`[↑]`[↑])])))).
  { fall v. fall d. fall d'. fintro Hd. fintro Hd'. fintro Hs. fintro HQv. fintro HvL.
    fmp HQv HvL. fex HQv Y HY. fdestr HY HY1 HY2.
    fassert HY' : (∃ LL d'`[↑] $0). { eapply LL_ex; eassumption. } fex HY' Y' HY'0.
    fexists Y'. fsplit; [exact HY'0|]. eapply sub0_use; [|exact HY2].
    eapply LL_sub with (a := d') (b := d); eassumption. }
  fassert Hc : (∃ (Ord0 $0 ∧ ∀ ($0 ∈' X`[↑]`[↑] → Qpow[$1 .: $0 .: (fun k => (var k)`[↑]`[↑])]))).
  { eapply ord_collect with (n := 0) (sg := var); eassumption. }
  fex Hc g Hg. fdestr Hg Hg1 Hg2.
  fassert HYg : (∃ LL g`[↑] $0). { eapply LL_ex; eassumption. } fex HYg Yg HYg0.
  fexists g. fexists Yg. fsplit; [fsplit; assumption|].
  fall v. fintro Hv. fintro HvL. finst Hg2 v. fmp Hg2 Hv. fmp Hg2 HvL. fex Hg2 Y0 HY0. fdestr HY0 HY01 HY02.
  fassert HE : (Y0 ≡' Yg). { eapply LL_unique with (a := g); eassumption. }
  exact (elem_cong HG v Y0 v Yg (eq_refl' HG v) HE HY02).
Qed.

End AxL2.

Section AxL3.
Context {G : list form} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G).

Lemma axL_power : incl powL_insts G -> G ⊢C rel Lform ax_power'.
Proof using HG HR HOm HL.
  intros Hpw. pose proof (Ax_cl_ord _ (Ax_L_cl _ HL)) as HO. pose proof (Ax_ord_prim _ HO) as HP.
  unfold ax_power'. cbn. fall x. fintro Hx.
  fassert Hp : (ax_power'). { apply Ctx, HG. cbn. tauto. }
  unfold ax_power' in Hp. finst Hp x. fex Hp P HP0.
  pose proof (L_bound HG HR HOm HL P Hpw) as Hbd. fex Hbd g Hg. fex Hg Yg HYg. fdestr HYg H12 Hg3. fdestr H12 Hg1 Hg2.
  apply (L_common HG HR HOm HL 1 (x .: var) g); [intros [|k] Hk; cbn; [exact Hx|lia] | exact Hg1 |].
  intros G' b Y HGG' Hb Hgb HY Hin. lift HGG'.
  assert (HYgY : G' ⊢C Sub0 Yg Y) by (eapply LL_sub with (a := b) (b := g); eassumption).
  assert (HT : G' ⊢C Trans0 Y) by (eapply LL_trans with (a := b); eassumption).
  pose proof (L_definable HG HR HOm HL 1 (∀ ($0 ∈' $1 → $0 ∈' $2)) (x .: var) b Y ltac:(fbcomp) Hb HY Hin) as HX.
  fex_raw HX X HX0. fdestr HX0 HXL HXd. simp_in HXL.
  fexists X. fsplit; [exact HXL|]. rewrite rel_is_power. fall z. fintro Hz.
  pose proof (def_mem (∀ ($0 ∈' $1 → $0 ∈' $2)) (x .: var) Y X z HXd) as Hm. simp_in Hm.
  fsplit.
  - fintro H. pose proof (iff_l _ _ _ Hm H) as H1. fdestr H1 HzY H2. apply (sub_subL HG HR HOm HL).
    unfold sub'. fall w. fintro Hwz. finst H2 w.
    fassert HwY : (w ∈' Y). { eapply trans0_use with (y := z); eassumption. }
    fmp H2 HwY. fmp H2 Hwz. exact H2.
  - fintro H. pose proof (subL_sub HG HR HOm HL z x Hz H) as Hs.
    pose proof HP0 as HP1. unfold is_power in HP1. finst HP1 z.
    pose proof (iff_r _ _ _ HP1 Hs) as HzP.
    finst Hg3 z. fmp Hg3 HzP. fmp Hg3 Hz.
    pose proof (sub0_use _ _ _ HYgY Hg3) as HzY.
    apply (iff_r _ _ _ Hm). fsplit; [exact HzY|]. fall w. fintro HwY. fintro Hwz.
    unfold sub' in Hs. finst Hs w. exact (IE Hs Hwz).
Qed.

Lemma rel_is_inductive t : rel Lform (is_inductive t) =
  (∃ (Lform ∧ (rel Lform (is_eset $0) ∧ $0 ∈' t`[↑]))) ∧
  ∀ (Lform → ($0 ∈' t`[↑] → ∃ (Lform ∧ (rel Lform (is_sigma $1 $0) ∧ $0 ∈' t`[↑]`[↑])))).
Proof. reflexivity. Qed.
Lemma rel_is_om w : rel Lform (is_om w) =
  rel Lform (is_inductive w) ∧ ∀ (Lform → rel Lform (is_inductive $0) → rel Lform (sub' w`[↑] $0)).
Proof. reflexivity. Qed.

Lemma axL_om0 : G ⊢C rel Lform ax_om'.
Proof using HG HR HOm HL.
  pose proof (Ax_cl_ord _ (Ax_L_cl _ HL)) as HO. pose proof (Ax_ord_prim _ HO) as HP.
  unfold ax_om'. cbn.
  fassert Hw : (∃ Om0 $0). { eapply om_ex; eassumption. } fex Hw w Hw0.
  fassert Hwo : (Ord0 w). { eapply om_ord; eassumption. }
  fassert HwL : (InL w). { eapply L_ord; eassumption. }
  fassert He : (∃ Emp0 $0). { eapply emp0_ex; eassumption. } fex He e He0.
  fassert Heo : (Ord0 e). { eapply ord_emp; eassumption. }
  fassert HeL : (InL e). { eapply L_ord; eassumption. }
  fexists w. fsplit; [exact HwL|]. rewrite rel_is_om, rel_is_inductive. fsplit; [fsplit|].
  - fexists e. fsplit; [exact HeL|]. fsplit.
    + rewrite rel_is_eset. fall z. fintro Hz. fintro Hze. pose proof He0 as He1. unfold Emp0 in He1.
      finst He1 z. exact (IE He1 Hze).
    + eapply om_emp; eassumption.
  - fall n. fintro HnL. fintro Hn.
    fassert Hs : (∃ Succ0 n`[↑] $0). { eapply succ0_ex; eassumption. } fex Hs s Hs0.
    fassert Hsw : (s ∈' w). { eapply om_succ with (n := n); eassumption. }
    fexists s. fsplit; [eapply inL_el with (x := w); eassumption|]. fsplit; [|exact Hsw].
    rewrite rel_is_sigma. fall z. fintro Hz.
    fassert Hsig : (is_sigma n s). { apply (iff_l _ _ _ (Succ0_iff HG HP n s) Hs0). }
    unfold is_sigma in Hsig. finst Hsig z. exact Hsig.
  - fall J. fintro HIL. fintro HI. rewrite rel_is_inductive in HI. fdestr HI HI1 HI2.
    apply (sub_subL HG HR HOm HL).
    fassert Hb1 : (∀ (Emp0 $0 → $0 ∈' J`[↑])).
    { fall e'. fintro He'. pose proof HI1 as HI1'. fex HI1' e0 He0'. fdestr He0' He0L He0'2.
      fdestr He0'2 He0e He0I. rewrite rel_is_eset in He0e.
      fassert Hemp : (Emp0 e0).
      { unfold Emp0. fall z. fintro Hz.
        fassert HzL : (InL z). { eapply inL_el with (x := e0); eassumption. }
        finst He0e z. fmp He0e HzL. exact (IE He0e Hz). }
      fassert HE : (e0 ≡' e'). { eapply emp0_unique; eassumption. }
      exact (elem_cong HG e0 J e' J HE (eq_refl' HG J) He0I). }
    fassert Hb2 : (∀ ($0 ∈' w`[↑] → $0 ∈' J`[↑] → ∀ (Succ0 $1 $0 → $0 ∈' J`[↑]`[↑]))).
    { fall n. fintro Hnw. fintro HnI. fall s. fintro Hs.
      fassert HnL : (InL n). { eapply inL_el with (x := J); eassumption. }
      pose proof HI2 as HI2'. finst HI2' n. fmp HI2' HnL. fmp HI2' HnI.
      fex HI2' s0 Hs0. fdestr Hs0 Hs0L Hs02. fdestr Hs02 Hs0s Hs0I. rewrite rel_is_sigma in Hs0s.
      fassert Hsig : (is_sigma n s0).
      { unfold is_sigma. fall z. fsplit.
        - fintro Hz. fassert HzL : (InL z). { eapply inL_el with (x := s0); eassumption. }
          finst Hs0s z. fmp Hs0s HzL. exact (iff_l _ _ _ Hs0s Hz).
        - fintro Hz. fassert HzL : (InL z).
          { fcases Hz Hz1 Hz2.
            - eapply inL_el with (x := n); eassumption.
            - exact (leib _ Lform n z HG (eq_sym' HG z n Hz2) HnL). }
          finst Hs0s z. fmp Hs0s HzL. exact (iff_r _ _ _ Hs0s Hz). }
      fassert Hsuc : (Succ0 n s0). { apply (iff_r _ _ _ (Succ0_iff HG HP n s0) Hsig). }
      fassert HE : (s0 ≡' s). { eapply succ0_unique with (x := n); eassumption. }
      exact (elem_cong HG s0 J s J HE (eq_refl' HG J) Hs0I). }
    fassert Hsub : (Sub0 w J). { eapply om_ind; eassumption. }
    exact Hsub.
Qed.

Lemma axL_base' a : In a ZF0base -> incl powL_insts G -> G ⊢C rel Lform a.
Proof using HG HR HOm HL.
  intros H Hpw. repeat (destruct H as [<-|H]); try destruct H.
  - exact (axL_refl HG HR HOm HL).
  - exact (axL_sym HG HR HOm HL).
  - exact (axL_trans HG HR HOm HL).
  - exact (axL_eq_elem HG HR HOm HL).
  - exact (axL_ext HG HR HOm HL).
  - exact (axL_eset HG HR HOm HL).
  - exact (axL_pair HG HR HOm HL).
  - exact (axL_union HG HR HOm HL).
  - exact (axL_power Hpw).
Qed.

Lemma axL_sep' n phi : fb (S n) phi -> incl (sepL_insts n phi) G -> G ⊢C rel Lform (forall_times n (ax_sep' phi)).
Proof using HG HR HOm HL.
  intros Hphi HI. pose proof (Ax_cl_ord _ (Ax_L_cl _ HL)) as HO. pose proof (Ax_ord_prim _ HO) as HP.
  assert (HI' : incl (refl_insts (S n) phi) G) by exact HI. clear HI.
  enough (H : G ⊢C (rel Lform (forall_times n (ax_sep' phi)))[var]) by (rewrite subst_var in H; exact H).
  apply (rel_ft Lform bounded_Lform). intros G' tau HGG' Htau _. lift HGG'.
  assert (Htau' : forall k, k < n -> G' ⊢C InL (tau k)) by exact Htau. clear Htau.
  rewrite relL_subst, rel_sep_eq. fall x. fintro Hx.
  fassert He : (∃ Emp0 $0). { eapply emp0_ex; eassumption. } fex He e He0.
  fassert Ho : (Ord0 e). { eapply ord_emp; eassumption. }
  apply (L_common HG HR HOm HL (S n) (x .: tau) e); [intros [|k] Hk; cbn; [exact Hx|apply Htau'; lia] | exact Ho |].
  intros G1 b Y HG1 Hb _ HY Hin. lift HG1.
  fassert Hr : (∃ ((Ord0 $0 ∧ b`[↑] ∈' $0) ∧ Refl (S n) phi $0)). { eapply reflection; eassumption. }
  fex_raw Hr be Hbe. fdestr Hbe Hbe1 HRf. fdestr Hbe1 Hbo Hbb. simp_in Hbo. simp_in Hbb.
  let GG := ctxof in assert (HRf2 : GG ⊢C Refl (S n) phi be).
  { replace (Refl (S n) phi be) with ((Refl (S n) phi $0)[be..]); [exact HRf|].
    rewrite (Refl_subst _ _ _ _ Hphi). reflexivity. }
  clear HRf. rename HRf2 into HRf.
  fassert HYb : (∃ LL be`[↑] $0). { eapply LL_ex; eassumption. } fex HYb Yb HYb0.
  fassert HYY : (Y ∈' Yb ∧ Sub0 Y Yb). { eapply LL_mono with (b := b); eassumption. }
  fdestr HYY HYin HYsub.
  let GG := ctxof in
  assert (Hin' : forall k, k < S n -> GG ⊢C (x .: tau) k ∈' Yb)
    by (intros k Hk; eapply sub0_use; [exact HYsub | apply Hin, Hk]).
  fassert HT : (Trans0 Yb). { eapply LL_trans with (a := be); eassumption. }
  pose proof (L_definable HG HR HOm HL (S n) (psiS phi) (x .: tau) be Yb (fb_psiS _ _ Hphi) Hbo HYb0 Hin') as HX.
  fex_raw HX X HX0. fdestr HX0 HXL HXd. simp_in HXL.
  fexists X. fsplit; [exact HXL|]. fall z. fintro Hz.
  pose proof (def_mem (psiS phi) (x .: tau) Yb X z HXd) as Hm.
  assert (E : (psiS phi)[z .: x .: tau] = z ∈' x ∧ phi[z .: tau]) by (unfold psiS; cbn [subst_form]; f_equal; fse).
  rewrite E in Hm. cbn [relS] in Hm.
  nphi phi (z .: tau).
  fsplit.
  - fintro H. pose proof (iff_l _ _ _ Hm H) as H1. fdestr H1 HzY H2. fdestr H2 Hzx Hphz. fsplit; [exact Hzx|].
    let GG := ctxof in
    assert (Hs : forall k, k < S n -> GG ⊢C (z .: tau) k ∈' Yb)
      by (intros [|k] Hk; [exact HzY | exact (Hin' (S k) ltac:(lia))]).
    fassert Hrf : (rel Lform (phi[z .: tau]) ↔ relS Yb (phi[z .: tau])). { eapply refl_use; eassumption. }
    exact (iff_r _ _ _ Hrf Hphz).
  - fintro H. fdestr H Hzx Hphz.
    fassert HzY : (z ∈' Yb). { eapply trans0_use with (y := x); [exact HT | exact (Hin' 0 ltac:(lia)) | exact Hzx]. }
    let GG := ctxof in
    assert (Hs : forall k, k < S n -> GG ⊢C (z .: tau) k ∈' Yb)
      by (intros [|k] Hk; [exact HzY | exact (Hin' (S k) ltac:(lia))]).
    fassert Hrf : (rel Lform (phi[z .: tau]) ↔ relS Yb (phi[z .: tau])). { eapply refl_use; eassumption. }
    apply (iff_r _ _ _ Hm). fsplit; [exact HzY|]. fsplit; [exact Hzx|]. exact (iff_l _ _ _ Hrf Hphz).
Qed.

Lemma axL_rep' n phi : fb (S (S n)) phi -> incl (repL_insts n phi) G ->
  G ⊢C rel Lform (forall_times n (ax_rep' phi)).
Proof using HG HR HOm HL.
  intros Hphi HI. pose proof (Ax_cl_ord _ (Ax_L_cl _ HL)) as HO. pose proof (Ax_ord_prim _ HO) as HP.
  assert (HIr : In (forall_times n (ax_rep' (repF phi))) G) by (apply HI; now left).
  assert (HIf : incl (refl_insts (S (S n)) (psiR phi)) G) by (intros a Ha; apply HI; right; apply in_app_iff; now left).
  assert (HIp : incl powL_insts G) by (intros a Ha; apply HI; right; apply in_app_iff; now right).
  clear HI. pose proof (fb_psiR _ _ Hphi) as HpsiR.
  enough (H : G ⊢C (rel Lform (forall_times n (ax_rep' phi)))[var]) by (rewrite subst_var in H; exact H).
  apply (rel_ft Lform bounded_Lform). intros G' tau HGG' Htau _. lift HGG'.
  assert (Htau' : forall k, k < n -> G' ⊢C InL (tau k)) by exact Htau. clear Htau.
  rewrite relL_subst, rel_rep_eq. fintro Hfun. fall x. fintro Hx.
  (* functionality of repF in V *)
  let GG := ctxof in
  assert (Hf : forall a b b', GG ⊢C (repF phi)[a .: b .: tau] → (repF phi)[a .: b' .: tau] → b ≡' b').
  { intros a b b'. unfold repF. simp. fintro H1. fintro H2. fdestr H1 H1a H1b. fdestr H1a Ha Hb.
    fdestr H2 H2a H2b. fdestr H2a Ha' Hb'.
    pose proof Hfun as Hf. finst Hf a. fmp Hf Ha. finst Hf b. fmp Hf Hb. finst Hf b'. fmp Hf Hb'.
    nphi_in Hf phi (a .: b .: tau). nphi_in Hf phi (a .: b' .: tau).
    nphi_in H1b phi (a .: b .: tau). nphi_in H2b phi (a .: b' .: tau).
    fmp Hf H1b. fmp Hf H2b. exact Hf. }
  let GG := ctxof in
  pose proof (rep_use GG n (repF phi) tau x HIr (fb_repF _ _ Hphi) Hf) as HZ.
  fex_raw HZ Zs HZ0.
  pose proof (L_bound HG HR HOm HL Zs HIp) as Hbd. fex Hbd g Hg. fex Hg Yg HYg. fdestr HYg H12 Hg3. fdestr H12 Hg1 Hg2.
  apply (L_common HG HR HOm HL (S n) (x .: tau) g); [intros [|k] Hk; cbn; [exact Hx|apply Htau'; lia] | exact Hg1 |].
  intros G1 b Y HG1 Hb Hgb HY Hin. lift HG1.
  assert (HYgY : G1 ⊢C Sub0 Yg Y) by (eapply LL_sub with (a := b) (b := g); eassumption).
  fassert Hr : (∃ ((Ord0 $0 ∧ b`[↑] ∈' $0) ∧ Refl (S (S n)) (psiR phi) $0)). { eapply reflection; eassumption. }
  fex_raw Hr be Hbe. fdestr Hbe Hbe1 HRf. fdestr Hbe1 Hbo Hbb. simp_in Hbo. simp_in Hbb.
  let GG := ctxof in assert (HRf2 : GG ⊢C Refl (S (S n)) (psiR phi) be).
  { replace (Refl (S (S n)) (psiR phi) be) with ((Refl (S (S n)) (psiR phi) $0)[be..]); [exact HRf|].
    rewrite (Refl_subst _ _ _ _ HpsiR). reflexivity. }
  clear HRf. rename HRf2 into HRf.
  fassert HYb : (∃ LL be`[↑] $0). { eapply LL_ex; eassumption. } fex HYb Yb HYb0.
  fassert HYY : (Y ∈' Yb ∧ Sub0 Y Yb). { eapply LL_mono with (b := b); eassumption. }
  fdestr HYY HYin HYsub.
  let GG := ctxof in
  assert (Hin' : forall k, k < S n -> GG ⊢C (x .: tau) k ∈' Yb)
    by (intros k Hk; eapply sub0_use; [exact HYsub | apply Hin, Hk]).
  pose proof (L_definable HG HR HOm HL (S n) (psiR phi) (x .: tau) be Yb HpsiR Hbo HYb0 Hin') as HX.
  fex_raw HX X HX0. fdestr HX0 HXL HXd. simp_in HXL.
  fexists X. fsplit; [exact HXL|]. fall v. fintro Hv.
  nphi phi ($0 .: v`[↑] .: (fun k => (tau k)`[↑])).
  pose proof (def_mem (psiR phi) (x .: tau) Yb X v HXd) as Hm.
  assert (E : (psiR phi)[v .: x .: tau] = ∃ ($0 ∈' x`[↑] ∧ phi[$0 .: v`[↑] .: (fun k => (tau k)`[↑])]))
    by (unfold psiR; cbn [subst_form]; f_equal; f_equal; fse).
  rewrite E in Hm.
  fsplit.
  - fintro H. pose proof (iff_l _ _ _ Hm H) as H1. fdestr H1 HvY H2.
    let GG := ctxof in
    assert (Hs : forall k, k < S (S n) -> GG ⊢C (v .: x .: tau) k ∈' Yb)
      by (intros [|k] Hk; [exact HvY | exact (Hin' k ltac:(lia))]).
    fassert Hrf : (rel Lform ((psiR phi)[v .: x .: tau]) ↔ relS Yb ((psiR phi)[v .: x .: tau])).
    { eapply refl_use; eassumption. }
    rewrite E in Hrf. exact (iff_r _ _ _ Hrf H2).
  - fintro H. pose proof H as H'.
    fassert HvZ : (v ∈' Zs).
    { apply (iff_r _ _ _ (rep_mem phi tau x Zs v HZ0)). fex H' u Hu. fdestr Hu HuL Hu2. fdestr Hu2 Hux Hphu.
      fexists u. fsplit; [exact Hux|]. fsplit; [fsplit; assumption|].
      nphi phi (u .: v .: tau). nphi_in Hphu phi (u .: v .: tau). exact Hphu. }
    finst Hg3 v. fmp Hg3 HvZ. fmp Hg3 Hv.
    pose proof (sub0_use _ _ _ HYsub (sub0_use _ _ _ HYgY Hg3)) as HvY.
    let GG := ctxof in
    assert (Hs : forall k, k < S (S n) -> GG ⊢C (v .: x .: tau) k ∈' Yb)
      by (intros [|k] Hk; [exact HvY | exact (Hin' k ltac:(lia))]).
    fassert Hrf : (rel Lform ((psiR phi)[v .: x .: tau]) ↔ relS Yb ((psiR phi)[v .: x .: tau])).
    { eapply refl_use; eassumption. }
    rewrite E in Hrf. apply (iff_r _ _ _ Hm). fsplit; [exact HvY|]. exact (iff_l _ _ _ Hrf H).
Qed.

End AxL3.

(** ** The statements used downstream *)
Section AxL.
Context {G : list form} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G).

(** the power set axiom needs the collection instance powL_insts (= oc_insts 0 Qpow) *)
Lemma axL_base a : In a ZF0base -> incl powL_insts G -> G ⊢C rel Lform a.
Proof using HG HR HOm HL. exact (axL_base' HG HR HOm HL a). Qed.
Lemma axL_om : G ⊢C rel Lform ax_om'.
Proof using HG HR HOm HL. exact (axL_om0 HG HR HOm HL). Qed.
Lemma axL_reg : G ⊢C rel Lform ax_reg'.
Proof using HG HR HOm HL. exact (axL_reg0 HG HR HOm HL). Qed.
Lemma axL_sep n phi : fb (S n) phi -> incl (sepL_insts n phi) G -> G ⊢C rel Lform (forall_times n (ax_sep' phi)).
Proof using HG HR HOm HL. exact (axL_sep' HG HR HOm HL n phi). Qed.
Lemma axL_rep n phi : fb (S (S n)) phi -> incl (repL_insts n phi) G -> G ⊢C rel Lform (forall_times n (ax_rep' phi)).
Proof using HG HR HOm HL. exact (axL_rep' HG HR HOm HL n phi). Qed.

End AxL.

(** packaged: each ZFR axiom holds in L, from finitely many further ZFR axioms *)
Theorem axL_ZFR a : ZFR a -> exists A, (forall b, In b A -> ZFR b) /\
  forall G, incl ZF0base G -> In ax_reg' G -> In ax_om' G -> incl Ax_L G -> incl A G -> G ⊢C rel Lform a.
Proof.
  intros [[[phi H | phi n H | phi n H] | ->] | ->].
  - exists powL_insts. split; [intros b Hb; exact (oc_insts_ok 0 Qpow b fb_Qpow Hb)|].
    intros G HG HR HOm HL HA. exact (axL_base' HG HR HOm HL phi H HA).
  - pose proof (fb_sep_inv _ _ H) as Hphi. exists (sepL_insts n phi).
    split; [intros b Hb; exact (sepL_insts_ok n phi b Hphi Hb)|].
    intros G HG HR HOm HL HA. exact (axL_sep HG HR HOm HL n phi Hphi HA).
  - pose proof (fb_rep_inv _ _ H) as Hphi. exists (repL_insts n phi).
    split; [intros b Hb; exact (repL_insts_ok n phi b Hphi Hb)|].
    intros G HG HR HOm HL HA. exact (axL_rep HG HR HOm HL n phi Hphi HA).
  - exists []. split; [intros b []|]. intros G HG HR HOm HL _. exact (axL_om HG HR HOm HL).
  - exists []. split; [intros b []|]. intros G HG HR HOm HL _. exact (axL_reg HG HR HOm HL).
Qed.
