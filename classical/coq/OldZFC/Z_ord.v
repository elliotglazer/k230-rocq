(** * Z_ord: ordinals (transitive sets of transitive sets; regularity available), ω,
    least-element and induction schemas, and the ordinal collection schema. *)
From Coq Require Import Arith Lia List.
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_setinf.
From OldZFC Require Import Z_rel Z_base Z_prim.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

(** ** Substitution conversion helpers *)
Lemma fconv {G} (phi : form) s1 s2 : G ⊢C phi[s1] -> (forall k, s1 k = s2 k) -> G ⊢C phi[s2].
Proof. intros H E. erewrite subst_ext; [exact H|]. intros k. symmetry. apply E. Qed.

Ltac sub_eq1 :=
  cbn; unfold funcomp; cbn; rewrite ?subst_term_comp;
  first [ reflexivity
        | (apply subst_term_id; intros; reflexivity)
        | (symmetry; apply subst_term_id; intros; reflexivity)
        | (apply subst_term_ext; intros; reflexivity) ].
Ltac sub_eq := let k := fresh "k" in intros [|[|[|k]]]; sub_eq1.
Ltac fconv_in H s2 :=
  rewrite ?subst_comp in H;
  let H' := fresh in pose proof (fconv _ _ s2 H) as H'; clear H; rename H' into H;
  specialize (H ltac:(sub_eq)).
Ltac fconv_goal s1 := rewrite ?subst_comp; apply (fconv _ s1); [|sub_eq].

(** trichotomy as a formula *)
Definition Tri (x y : term) : form := x ∈' y ∨ x ≡' y ∨ y ∈' x.
#[global] Arguments Tri : simpl never.
Lemma Tri_subst x y sg : (Tri x y)[sg] = Tri x`[sg] y`[sg].
Proof. psubst Tri. Qed.
#[global] Hint Rewrite Tri_subst : fsub.

(** separation formulas used here *)
Definition tri_form1 : form := ∃ ($0 ∈' $2 ∧ ¬ Tri $1 $0).
Definition tri_form2 : form := ¬ Tri $1 $0.
Definition om_form : form := Ord0 $0 ∧ Sub0 $0 $1 ∧ (Emp0 $0 ∨ ∃ ($0 ∈' $1 ∧ Succ0 $0 $1)).
Definition notin_form : form := ¬ ($0 ∈' $1).

Lemma fb_tri1 : fb 2 tri_form1.
Proof. unfold tri_form1, Tri. cbn. lia. Qed.
Lemma fb_tri2 : fb 2 tri_form2.
Proof. unfold tri_form2, Tri. cbn. lia. Qed.
Lemma fb_om : fb 2 om_form.
Proof. unfold om_form, Ord0, Trans0, Sub0, Emp0, Succ0, Sub0. cbn. lia. Qed.
Lemma fb_notin : fb 2 notin_form.
Proof. unfold notin_form. cbn. lia. Qed.

(** fixed instances used by this file (to be filled by the proofs); includes Ax_prim *)
Definition Ax_ord : list form := Ax_prim ++
  [forall_times 1 (ax_sep' tri_form1); forall_times 1 (ax_sep' tri_form2);
   forall_times 1 (ax_sep' om_form); forall_times 1 (ax_sep' notin_form)].
Lemma Ax_ord_ok a : In a Ax_ord -> ZFR a.
Proof.
  intros H. apply in_app_iff in H as [H|H]; [now apply Ax_prim_ok|].
  destruct H as [<-|[<-|[<-|[<-|[]]]]]; apply ZFR_sep.
  - exact fb_tri1. - exact fb_tri2. - exact fb_om. - exact fb_notin.
Qed.
Lemma Ax_ord_prim G : incl Ax_ord G -> incl Ax_prim G.
Proof. intros H a Ha. apply H, in_app_iff. now left. Qed.

Lemma in_tri1 G : incl Ax_ord G -> In (forall_times 1 (ax_sep' tri_form1)) G.
Proof. intros H. apply H, in_app_iff. right. cbn. tauto. Qed.
Lemma in_tri2 G : incl Ax_ord G -> In (forall_times 1 (ax_sep' tri_form2)) G.
Proof. intros H. apply H, in_app_iff. right. cbn. tauto. Qed.
Lemma in_om G : incl Ax_ord G -> In (forall_times 1 (ax_sep' om_form)) G.
Proof. intros H. apply H, in_app_iff. right. cbn. tauto. Qed.
Lemma in_notin G : incl Ax_ord G -> In (forall_times 1 (ax_sep' notin_form)) G.
Proof. intros H. apply H, in_app_iff. right. cbn. tauto. Qed.

(** ** Regularity *)
Lemma reg_use {G} (HG : incl ZF0base G) (HR : In ax_reg' G) x y : G ⊢C y ∈' x ->
  G ⊢C ∃ ($0 ∈' x`[↑] ∧ ∀ ($0 ∈' $1 → ¬ ($0 ∈' x`[↑]`[↑]))).
Proof.
  intros Hy. assert (H : G ⊢C ax_reg') by (apply Ctx, HR). unfold MinZF.ax_reg' in H.
  finst H x. apply (IE H). fexists y. exact Hy.
Qed.

Lemma no_self_g {G} (HG : incl ZF0base G) (HR : In ax_reg' G) x : G ⊢C x ∈' x -> G ⊢C ⊥.
Proof.
  intros Hx. fobtain (sing_ex HG x) as s Hs. fhave Hxs : (sing_in HG x s Hs).
  fhave T : (reg_use HG HR s x Hxs). fex T m Hm. fdestr Hm Hm1 Hm2.
  fhave E : (sing_el HG x s m Hs Hm1). finst Hm2 x. fassert Hxm : (x ∈' m); [fmem|]. exact (IE (IE Hm2 Hxm) Hxs).
Qed.

Lemma no_cycle2_g {G} (HG : incl ZF0base G) (HR : In ax_reg' G) x y : G ⊢C x ∈' y -> G ⊢C y ∈' x -> G ⊢C ⊥.
Proof.
  intros Hxy Hyx. fobtain (pair_ex HG x y) as p Hp. fhave Hxp : (pair_l HG x y p Hp).
  fhave Hyp : (pair_r HG x y p Hp).
  fhave T : (reg_use HG HR p x Hxp). fex T m Hm. fdestr Hm Hm1 Hm2.
  fhave E : (pair_el HG x y p m Hp Hm1). fcases E E1 E2.
  - finst Hm2 y. fassert Hh : (y ∈' m); [fmem|]. exact (IE (IE Hm2 Hh) Hyp).
  - finst Hm2 x. fassert Hh : (x ∈' m); [fmem|]. exact (IE (IE Hm2 Hh) Hxp).
Qed.

(** ** Basic ordinal facts *)
Lemma ord_tr_g {G} a x y : G ⊢C Ord0 a -> G ⊢C x ∈' y -> G ⊢C y ∈' a -> G ⊢C x ∈' a.
Proof.
  intros H Hxy Hya. unfold Ord0 in H. fdestr H H1 H2. unfold Trans0 in H1. finst H1 y. fmp H1 Hya.
  finst H1 x. exact (IE H1 Hxy).
Qed.

Lemma ord_trans_el {G} a x : G ⊢C Ord0 a -> G ⊢C x ∈' a -> G ⊢C Trans0 x.
Proof. intros H Hx. unfold Ord0 in H. fdestr H H1 H2. finst H2 x. exact (IE H2 Hx). Qed.

Lemma ord_el_g {G} a x : G ⊢C Ord0 a -> G ⊢C x ∈' a -> G ⊢C Ord0 x.
Proof.
  intros H Hx. unfold Ord0. fsplit.
  - exact (ord_trans_el a x H Hx).
  - fall y. fintro Hy. apply (ord_trans_el a y H). exact (ord_tr_g a y x H Hy Hx).
Qed.

Lemma ord_el_sub_g {G} a b : G ⊢C Ord0 b -> G ⊢C a ∈' b -> G ⊢C Sub0 a b.
Proof. intros H Ha. unfold Sub0. fall z. fintro Hz. exact (ord_tr_g b z a H Hz Ha). Qed.

Lemma ord_emp_g {G} e : G ⊢C Emp0 e -> G ⊢C Ord0 e.
Proof.
  intros H. unfold Ord0, Trans0. fsplit.
  - fall z. fintro Hz. fabsurd. unfold Emp0 in H. finst H z. exact (IE H Hz).
  - fall z. fintro Hz. fabsurd. unfold Emp0 in H. finst H z. exact (IE H Hz).
Qed.

Lemma ord_succ_g {G} (HG : incl ZF0base G) a s : G ⊢C Ord0 a -> G ⊢C Succ0 a s -> G ⊢C Ord0 s.
Proof.
  intros Ha Hs. apply (succ0_to HG) in Hs. unfold Ord0. fsplit.
  - unfold Trans0. fall z. fintro Hz. fall w. fintro Hw. apply (succ_in_l HG a s w Hs).
    fhave T : (succ_el HG a s z Hs Hz). fcases T T1 T2.
    + exact (ord_tr_g a w z Ha Hw T1).
    + fmem.
  - fall z. fintro Hz. fhave T : (succ_el HG a s z Hs Hz). fcases T T1 T2.
    + exact (ord_trans_el a z Ha T1).
    + unfold Ord0 in Ha. fdestr Ha Ha1 Ha2. frew T2 (Trans0 $0). exact Ha1.
Qed.

Lemma ord_tri_g {G} (HG : incl ZF0base G) (HR : In ax_reg' G)
  (H1 : In (forall_times 1 (ax_sep' tri_form1)) G) (H2 : In (forall_times 1 (ax_sep' tri_form2)) G) a b :
  G ⊢C Ord0 a -> G ⊢C Ord0 b -> G ⊢C Tri a b.
Proof.
  intros Ha Hb. fcontra Hn.
  fobtain (succ_ex HG a) as A HA. fobtain (succ_ex HG b) as B HB.
  fhave HoA : (ord_succ_g HG a A Ha (succ0_of HG a A HA)).
  fhave HoB : (ord_succ_g HG b B Hb (succ0_of HG b B HB)).
  pose proof (sep_use _ 1 tri_form1 (B .: var) A H1 fb_tri1) as T. unfold tri_form1 in T. simp_in T.
  fex T X HX.
  fassert HaX : (a ∈' X).
  { pose proof HX as H. finst H a. apply (iff_r _ _ _ H). fsplit; [exact (succ_self HG a A HA)|].
    fexists b. fsplit; [exact (succ_self HG b B HB)|exact Hn]. }
  fhave T : (reg_use HG HR X a HaX). fex T x0 Hx0. fdestr Hx0 Hx0X Hx0m.
  pose proof HX as H. finst H x0. fhave Hx0' : (iff_l _ _ _ H Hx0X). clear H.
  fdestr Hx0' Hx0A Hx0e. fex Hx0e y1 Hy1. fdestr Hy1 Hy1B Hy1n.
  pose proof (sep_use _ 1 tri_form2 (x0 .: var) B H2 fb_tri2) as T. unfold tri_form2 in T. simp_in T.
  fex T Y HY.
  fassert Hy1Y : (y1 ∈' Y).
  { pose proof HY as H. finst H y1. apply (iff_r _ _ _ H). fsplit; assumption. }
  fhave T : (reg_use HG HR Y y1 Hy1Y). fex T y0 Hy0. fdestr Hy0 Hy0Y Hy0m.
  pose proof HY as H. finst H y0. fhave Hy0' : (iff_l _ _ _ H Hy0Y). clear H. fdestr Hy0' Hy0B Hy0n.
  fhave Hox : (ord_el_g A x0 HoA Hx0A). fhave Hoy : (ord_el_g B y0 HoB Hy0B).
  fassert Hsub1 : (sub' x0 y0).
  { unfold sub'. fall z. fintro Hz.
    fhave HzA : (ord_tr_g A z x0 HoA Hz Hx0A).
    fassert Ht : (Tri z y0).
    { fcontra Hc. finst Hx0m z. fmp Hx0m Hz. apply (IE Hx0m). pose proof HX as H. finst H z.
      apply (iff_r _ _ _ H). fsplit; [exact HzA|]. fexists y0. fsplit; [exact Hy0B|exact Hc]. }
    unfold Tri in Ht. fcases Ht Hl Ht3; [fcases Hl Ht1 Ht2|].
    + exact Ht1.
    + fabsurd. apply (IE Hy0n). unfold Tri. fright. fmem.
    + fabsurd. apply (IE Hy0n). unfold Tri. fright. exact (ord_tr_g x0 y0 z Hox Ht3 Hz). }
  fassert Hsub2 : (sub' y0 x0).
  { unfold sub'. fall w. fintro Hw.
    fhave HwB : (ord_tr_g B w y0 HoB Hw Hy0B).
    fassert Ht : (Tri x0 w).
    { fcontra Hc. finst Hy0m w. fmp Hy0m Hw. apply (IE Hy0m). pose proof HY as H. finst H w.
      apply (iff_r _ _ _ H). fsplit; [exact HwB|exact Hc]. }
    unfold Tri in Ht. fcases Ht Hl Ht3; [fcases Hl Ht1 Ht2|].
    + fabsurd. apply (IE Hy0n). unfold Tri. fleft. fleft. exact (ord_tr_g y0 x0 w Hoy Ht1 Hw).
    + fabsurd. apply (IE Hy0n). unfold Tri. fleft. fleft. fmem.
    + exact Ht3. }
  fhave E : (ext_rule HG x0 y0 Hsub1 Hsub2). apply (IE Hy0n). unfold Tri. fleft. fright. exact E.
Qed.

Lemma ord_sub_g {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HO : incl Ax_ord G) a b :
  G ⊢C Ord0 a -> G ⊢C Ord0 b -> G ⊢C Sub0 a b -> G ⊢C a ∈' b ∨ a ≡' b.
Proof.
  intros Ha Hb Hs. fhave T : (ord_tri_g HG HR (in_tri1 _ HO) (in_tri2 _ HO) a b Ha Hb).
  unfold Tri in T. fcases T Hl H3; [exact Hl|]. fabsurd. unfold Sub0 in Hs. finst Hs b. fmp Hs H3.
  exact (no_self_g HG HR b Hs).
Qed.

Lemma ord_succ_le_g {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HO : incl Ax_ord G) a b s :
  G ⊢C Ord0 a -> G ⊢C Ord0 b -> G ⊢C a ∈' b -> G ⊢C Succ0 a s -> G ⊢C s ∈' b ∨ s ≡' b.
Proof.
  intros Ha Hb Hab Hs. apply (ord_sub_g HG HR HO); [exact (ord_succ_g HG a s Ha Hs)|exact Hb|].
  apply (succ0_to HG) in Hs. unfold Sub0. fall z. fintro Hz. fhave T : (succ_el HG a s z Hs Hz).
  fcases T T1 T2; [exact (ord_tr_g b z a Hb T1 Hab)|fmem].
Qed.

Lemma ord_union_g {G} (HG : incl ZF0base G) X u :
  G ⊢C ∀ ($0 ∈' X`[↑] → Ord0 $0) -> G ⊢C Union0 X u -> G ⊢C Ord0 u.
Proof.
  intros HX Hu. apply (union0_to HG) in Hu. unfold Ord0. fsplit.
  - unfold Trans0. fall z. fintro Hz. fall w. fintro Hw. fhave T : (union_el HG X u z Hu Hz).
    fex T y Hy. fdestr Hy Hy1 Hy2. finst HX y. fmp HX Hy1.
    exact (union_in HG X u y w Hu Hy1 (ord_tr_g y w z HX Hw Hy2)).
  - fall z. fintro Hz. fhave T : (union_el HG X u z Hu Hz).
    fex T y Hy. fdestr Hy Hy1 Hy2. finst HX y. fmp HX Hy1. exact (ord_trans_el y z HX Hy2).
Qed.

Lemma ord_cases_g {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HO : incl Ax_ord G) a :
  G ⊢C Ord0 a -> G ⊢C Emp0 a ∨ (∃ (Ord0 $0 ∧ Succ0 $0 a`[↑])) ∨ Lim0 a.
Proof.
  intros Ha. apply (XM_rule _ (Emp0 a)).
  { fintro He. fleft. fleft. exact He. }
  fintro Hne. apply (XM_rule _ (∀ ($0 ∈' a`[↑] → ∃ ($0 ∈' a`[↑]`[↑] ∧ $1 ∈' $0)))).
  - fintro Hl. fright. unfold Lim0. fsplit; [fsplit; [exact Ha|]|exact Hl].
    fcontra Hc. apply (IE Hne). unfold Emp0. fall z. fintro Hz. apply (IE Hc). fexists z.
    fsplit; [exact Hz|apply (eq_refl' HG)].
  - fintro Hnl. fleft. fright. fcontra Hc. apply (IE Hnl). fall z. fintro Hz. fcontra Hc2.
    apply (IE Hc). fexists z. fsplit; [exact (ord_el_g a z Ha Hz)|].
    unfold Succ0. fsplit; [fsplit; [exact Hz|exact (ord_el_sub_g z a Ha Hz)]|].
    fall w. fintro Hw. fhave Hoz : (ord_el_g a z Ha Hz). fhave How : (ord_el_g a w Ha Hw).
    fhave T : (ord_tri_g HG HR (in_tri1 _ HO) (in_tri2 _ HO) w z How Hoz). unfold Tri in T.
    fcases T Hl H3; [exact Hl|]. fabsurd. apply (IE Hc2). fexists w. fsplit; assumption.
Qed.

Lemma lim_succ_g {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HO : incl Ax_ord G) l a s :
  G ⊢C Lim0 l -> G ⊢C a ∈' l -> G ⊢C Succ0 a s -> G ⊢C s ∈' l.
Proof.
  intros H Ha Hs. unfold Lim0 in H. fdestr H H12 H3. fdestr H12 Hol Hne. finst H3 a. fmp H3 Ha.
  fex H3 w Hw. fdestr Hw Hwl Haw.
  fhave T : (ord_succ_le_g HG HR HO a w s (ord_el_g l a Hol Ha) (ord_el_g l w Hol Hwl) Haw Hs).
  fcases T T1 T2; [exact (ord_tr_g l s w Hol T1 Hwl)|fmem].
Qed.

Lemma ord_max_g {G} (HG : incl ZF0base G) a b : G ⊢C Ord0 a -> G ⊢C Ord0 b ->
  G ⊢C ∃ (Ord0 $0 ∧ Sub0 a`[↑] $0 ∧ Sub0 b`[↑] $0).
Proof.
  intros Ha Hb. fobtain (pair_ex HG a b) as p Hp. fobtain (union_ex HG p) as u Hu. fexists u.
  fsplit; [fsplit|].
  - apply (ord_union_g HG p u); [|exact (union0_of HG p u Hu)]. fall z. fintro Hz.
    fhave T : (pair_el HG a b p z Hp Hz). fcases T T1 T2.
    + frew T1 (Ord0 $0). exact Ha.
    + frew T2 (Ord0 $0). exact Hb.
  - unfold Sub0. fall z. fintro Hz. exact (union_in HG p u a z Hu (pair_l HG a b p Hp) Hz).
  - unfold Sub0. fall z. fintro Hz. exact (union_in HG p u b z Hu (pair_r HG a b p Hp) Hz).
Qed.

(** ** ω *)
Lemma om_ex_g {G} (HG : incl ZF0base G) (HO : incl Ax_ord G) : In ax_om' G -> G ⊢C ∃ Om0 $0.
Proof.
  intros Hom. assert (H : G ⊢C ax_om') by (apply Ctx, Hom). rewrite ax_om'_eq in H.
  fex H W HW. unfold is_om in HW. fdestr HW HInd HMin.
  pose proof (sep_use _ 1 om_form (W .: var) W (in_om _ HO) fb_om) as T. unfold om_form in T. simp_in T.
  fex T X HX.
  fassert HXi : (is_inductive X).
  { unfold is_inductive. fsplit.
    - fhave T : (ind_e W HInd). fex T e He. fdestr He He1 He2. fexists e. fsplit; [exact He1|].
      pose proof HX as H. finst H e. apply (iff_r _ _ _ H). clear H. fsplit; [exact He2|].
      fsplit; [fsplit|].
      + exact (ord_emp_g e (emp0_of e He1)).
      + unfold Sub0. fall z. fintro Hz. fabsurd. exact (eset_el HG e z He1 Hz).
      + fleft. exact He1.
    - fall u. fintro Hu. pose proof HX as H. finst H u. fhave Hu' : (iff_l _ _ _ H Hu). clear H.
      fdestr Hu' HuW HuP. fdestr HuP HuP12 HuP3. fdestr HuP12 Huo Hus.
      fhave T : (ind_s W u HInd HuW). fex T s Hs. fdestr Hs Hs1 Hs2.
      fexists s. fsplit; [exact Hs1|].
      pose proof HX as H. finst H s. apply (iff_r _ _ _ H). clear H. fsplit; [exact Hs2|].
      fsplit; [fsplit|].
      + exact (ord_succ_g HG u s Huo (succ0_of HG u s Hs1)).
      + unfold Sub0. fall z. fintro Hz. fhave T : (succ_el HG u s z Hs1 Hz). fcases T T1 T2.
        * unfold Sub0 in Hus. finst Hus z. exact (IE Hus T1).
        * fmem.
      + fright. fexists u. fsplit; [exact (succ_self HG u s Hs1)|exact (succ0_of HG u s Hs1)]. }
  finst HMin X. fmp HMin HXi.
  fassert HP : (∀ ($0 ∈' W`[↑] → Ord0 $0 ∧ Sub0 $0 W`[↑] ∧ (Emp0 $0 ∨ ∃ ($0 ∈' $1 ∧ Succ0 $0 $1)))).
  { fall n. fintro Hn. unfold sub' in HMin. finst HMin n. fmp HMin Hn. pose proof HX as H. finst H n.
    exact (CE2 (iff_l _ _ _ H HMin)). }
  fexists W. unfold Om0. fsplit.
  - unfold Lim0. fsplit; [fsplit|].
    + unfold Ord0. fsplit.
      * unfold Trans0. fall z. fintro Hz. fall y. fintro Hy. finst HP z. fmp HP Hz.
        fdestr HP HP12 HP3. fdestr HP12 HP1 HP2. unfold Sub0 in HP2. finst HP2 y. exact (IE HP2 Hy).
      * fall z. fintro Hz. finst HP z. fmp HP Hz.
        fdestr HP HP12 HP3. fdestr HP12 HP1 HP2. unfold Ord0 in HP1. exact (CE1 HP1).
    + fhave T : (ind_e W HInd). fex T e He. fdestr He He1 He2. fexists e.
      fsplit; [exact He2|apply (eq_refl' HG)].
    + fall z. fintro Hz. fhave T : (ind_s W z HInd Hz). fex T s Hs. fdestr Hs Hs1 Hs2. fexists s.
      fsplit; [exact Hs2|exact (succ_self HG z s Hs1)].
  - fall n. fintro Hn. finst HP n. fmp HP Hn. exact (CE2 HP).
Qed.

Lemma om_ord_g {G} w : G ⊢C Om0 w -> G ⊢C Ord0 w.
Proof. intros H. unfold Om0, Lim0 in H. exact (CE1 (CE1 (CE1 H))). Qed.

Lemma lim_not_emp {G} w : G ⊢C Lim0 w -> G ⊢C Emp0 w -> G ⊢C ⊥.
Proof.
  intros H He. unfold Lim0 in H. fdestr H H12 H3. fdestr H12 H1 H2. fex H2 z Hz. fdestr Hz Hz1 Hz2.
  unfold Emp0 in He. finst He z. exact (IE He Hz1).
Qed.

Lemma lim_not_succ {G} (HG : incl ZF0base G) (HR : In ax_reg' G) w m : G ⊢C Lim0 w -> G ⊢C Succ0 m w -> G ⊢C ⊥.
Proof.
  intros H Hs. apply (succ0_to HG) in Hs. fhave Hm : (succ_self HG m w Hs).
  unfold Lim0 in H. fdestr H H12 H3. finst H3 m. fmp H3 Hm. fex H3 k Hk. fdestr Hk Hk1 Hk2.
  fhave T : (succ_el HG m w k Hs Hk1). fcases T T1 T2.
  - exact (no_cycle2_g HG HR m k Hk2 T1).
  - apply (no_self_g HG HR m). fmem.
Qed.

Lemma om_el_g {G} w n : G ⊢C Om0 w -> G ⊢C n ∈' w -> G ⊢C Emp0 n ∨ ∃ ($0 ∈' w`[↑] ∧ Succ0 $0 n`[↑]).
Proof.
  intros H Hn. fhave Ho : (om_ord_g w H). unfold Om0 in H. fdestr H Hl H2. finst H2 n. fmp H2 Hn.
  fcases H2 E1 E2; [fleft; exact E1|]. fright. fex E2 m Hm. fdestr Hm Hm1 Hm2. fexists m.
  fsplit; [exact (ord_tr_g w m n Ho Hm1 Hn)|exact Hm2].
Qed.

Lemma om_not_el {G} (HG : incl ZF0base G) (HR : In ax_reg' G) w w' : G ⊢C Om0 w -> G ⊢C Om0 w' -> G ⊢C w ∈' w' -> G ⊢C ⊥.
Proof.
  intros H H' Hin. fhave T : (om_el_g w' w H' Hin). unfold Om0 in H. fdestr H Hl H2.
  fcases T T1 T2.
  - exact (lim_not_emp w Hl T1).
  - fex T2 m Hm. fdestr Hm Hm1 Hm2. exact (lim_not_succ HG HR w m Hl Hm2).
Qed.

Lemma om_unique_g {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HO : incl Ax_ord G) w w' :
  G ⊢C Om0 w -> G ⊢C Om0 w' -> G ⊢C w ≡' w'.
Proof.
  intros H H'. fhave T : (ord_tri_g HG HR (in_tri1 _ HO) (in_tri2 _ HO) w w' (om_ord_g w H) (om_ord_g w' H')).
  unfold Tri in T. fcases T Hl H3; [fcases Hl H1 H2|].
  - fabsurd. exact (om_not_el HG HR w w' H H' H1).
  - exact H2.
  - fabsurd. exact (om_not_el HG HR w' w H' H H3).
Qed.

Lemma om_emp_g {G} (HG : incl ZF0base G) (HR : In ax_reg' G) w e : G ⊢C Om0 w -> G ⊢C Emp0 e -> G ⊢C e ∈' w.
Proof.
  intros H He. fhave Ho : (om_ord_g w H). unfold Om0, Lim0 in H. fdestr H Hl H2. fdestr Hl Hl12 Hl3.
  fdestr Hl12 Hl1 Hne. fex Hne z Hz. fdestr Hz Hz1 Hz2.
  fhave T : (reg_use HG HR w z Hz1). fex T m Hm. fdestr Hm Hm1 Hm2.
  fassert Hme : (is_eset m).
  { unfold is_eset. fall y. fintro Hy. finst Hm2 y. fmp Hm2 Hy. apply (IE Hm2). exact (ord_tr_g w y m Ho Hy Hm1). }
  fhave E : (eset_unique HG m e Hme (emp0_to e He)). fmem.
Qed.

Lemma om_ind_g {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HO : incl Ax_ord G) w X : G ⊢C Om0 w ->
  G ⊢C ∀ (Emp0 $0 → $0 ∈' X`[↑]) ->
  G ⊢C ∀ ($0 ∈' w`[↑] → $0 ∈' X`[↑] → ∀ (Succ0 $1 $0 → $0 ∈' X`[↑]`[↑])) ->
  G ⊢C Sub0 w X.
Proof.
  intros H H0 HS. fhave Ho : (om_ord_g w H). unfold Sub0. fall z. fintro Hz. fcontra Hzn.
  pose proof (sep_use _ 1 notin_form (X .: var) w (in_notin _ HO) fb_notin) as T. unfold notin_form in T.
  simp_in T. fex T D HD.
  fassert HzD : (z ∈' D). { pose proof HD as H'. finst H' z. apply (iff_r _ _ _ H'). fsplit; assumption. }
  fhave T : (reg_use HG HR D z HzD). fex T m Hm. fdestr Hm Hm1 Hm2.
  pose proof HD as H'. finst H' m. fhave Hm' : (iff_l _ _ _ H' Hm1). clear H'. fdestr Hm' HmW HmX.
  fhave T : (om_el_g w m H HmW). fcases T T1 T2.
  - apply (IE HmX). finst H0 m. exact (IE H0 T1).
  - fex T2 k Hk. fdestr Hk Hk1 Hk2. apply (IE HmX).
    fhave Hkm : (succ_self HG k m (succ0_to HG k m Hk2)).
    fassert HkX : (k ∈' X).
    { fcontra Hc. finst Hm2 k. fmp Hm2 Hkm. apply (IE Hm2). pose proof HD as H'. finst H' k.
      apply (iff_r _ _ _ H'). fsplit; assumption. }
    finst HS k. fmp HS Hk1. fmp HS HkX. finst HS m. exact (IE HS Hk2).
Qed.

(** ** Schemas *)
(** instances for the least-element schema of a formula [psi] ($0 = the ordinal, $1.. = params) *)
Definition least_inst (n : nat) (psi : form) : form := forall_times n (ax_sep' psi).

(** δ is the least ordinal with Q(δ, v): $0 = v, $1 = δ, $(k+2) = parameter k *)
Definition oc_form (Q : form) : form :=
  Ord0 $1 ∧ Q[$1 .: $0 .: (fun k => $(S (S k)))] ∧ ∀ ($0 ∈' $2 → ¬ Q[$0 .: $1 .: (fun k => $(S (S (S k))))]).
#[global] Arguments oc_form : simpl never.

Lemma fb_oc n Q : fb (S (S n)) Q -> fb (S (S n)) (oc_form Q).
Proof.
  intros HQ. unfold oc_form, Ord0, Trans0. cbn. repeat split; try lia.
  - eapply fb_subst; [exact HQ|]. intros [|[|i]] Hi; cbn; lia.
  - eapply fb_subst; [exact HQ|]. intros [|[|i]] Hi; cbn; lia.
Qed.

(** instances for the ordinal collection schema of [Q] ($0 = δ, $1 = v, $2.. = params) *)
Definition oc_insts (n : nat) (Q : form) : list form :=
  [least_inst (S n) Q; forall_times n (ax_rep' (oc_form Q))].
Lemma oc_insts_ok n Q a : fb (S (S n)) Q -> In a (oc_insts n Q) -> ZFR a.
Proof.
  intros HQ [<-|[<-|[]]].
  - apply ZFR_sep. exact HQ.
  - apply ZFR_rep. now apply fb_oc.
Qed.

Lemma least_ord_g {G} (HG : incl ZF0base G) (HR : In ax_reg' G) n psi sg a : fb (S n) psi -> In (least_inst n psi) G ->
  G ⊢C Ord0 a -> G ⊢C psi[a .: sg] ->
  G ⊢C ∃ (Ord0 $0 ∧ psi[up sg] ∧ ∀ ($0 ∈' $1 → ¬ psi[up (sg >> subst_term ↑)])).
Proof.
  intros Hfb Hin Ha Hp. unfold least_inst in Hin.
  fobtain (succ_ex HG a) as A HA.
  fhave HoA : (ord_succ_g HG a A Ha (succ0_of HG a A HA)).
  pose proof (sep_use _ n psi sg A Hin Hfb) as T. fex T Sx HS.
  fassert HaS : (a ∈' Sx).
  { pose proof HS as H. finst H a. apply (iff_r _ _ _ H). fsplit; [exact (succ_self HG a A HA)|].
    fconv_goal (a .: sg). exact Hp. }
  fhave T : (reg_use HG HR Sx a HaS). fex T m Hm. fdestr Hm Hm1 Hm2.
  pose proof HS as H. finst H m. fhave Hm' : (iff_l _ _ _ H Hm1). clear H. fdestr Hm' HmA Hmp.
  fexists m. fsplit; [fsplit|].
  - exact (ord_el_g A m HoA HmA).
  - fconv_in Hmp (m .: sg). fconv_goal (m .: sg). exact Hmp.
  - fall g. fintro Hg. fintro Hpg. finst Hm2 g. fmp Hm2 Hg. apply (IE Hm2). pose proof HS as H. finst H g.
    apply (iff_r _ _ _ H). fsplit; [exact (ord_tr_g A g m HoA Hg HmA)|].
    fconv_in Hpg (g .: sg). fconv_goal (g .: sg). exact Hpg.
Qed.

Lemma ord_ind_g {G} (HG : incl ZF0base G) (HR : In ax_reg' G) n psi sg a : fb (S n) psi -> In (least_inst n (¬ psi)) G ->
  G ⊢C ∀ (Ord0 $0 → (∀ ($0 ∈' $1 → psi[up (sg >> subst_term ↑)])) → psi[up sg]) ->
  G ⊢C Ord0 a -> G ⊢C psi[a .: sg].
Proof.
  intros Hfb Hin H Ha. fcontra Hn.
  assert (Hfb' : fb (S n) (¬ psi)) by (cbn; tauto).
  fhave T : (least_ord_g HG HR n (¬ psi) sg a Hfb' Hin Ha Hn). fex T m Hm.
  fdestr Hm Hm12 Hm3. fdestr Hm12 Hmo Hmn.
  finst H m. fmp H Hmo.
  fassert Hall : (∀ ($0 ∈' m`[↑] → psi[up (sg >> subst_term ↑)][up m..])).
  { fall g. fintro Hg. fcontra Hc. finst Hm3 g. fmp Hm3 Hg. apply (IE Hm3). fintro Hp'.
    apply (IE Hc). fconv_goal (g .: sg). fconv_in Hp' (g .: sg). exact Hp'. }
  simp_in Hall. fmp H Hall. apply (IE Hmn). fconv_goal (m .: sg). fconv_in H (m .: sg). exact H.
Qed.

Lemma ord_collect_g {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HO : incl Ax_ord G) n Q sg X :
  fb (S (S n)) Q -> incl (oc_insts n Q) G ->
  G ⊢C ∀ ($0 ∈' X`[↑] → ∃ (Ord0 $0 ∧ Q[up (up sg)])) ->
  G ⊢C ∀ (∀ (∀ (Ord0 $1 → Ord0 $0 → Sub0 $1 $0 →
                Q[$1 .: $2 .: (fun k => (sg k)`[↑]`[↑]`[↑])] → Q[$0 .: $2 .: (fun k => (sg k)`[↑]`[↑]`[↑])]))) ->
  G ⊢C ∃ (Ord0 $0 ∧ ∀ ($0 ∈' X`[↑]`[↑] → Q[$1 .: $0 .: (fun k => (sg k)`[↑]`[↑])])).
Proof.
  intros Hfb Hi Hall Hmono.
  assert (Hl : In (least_inst (S n) Q) G) by (apply Hi; cbn; tauto).
  assert (Hr : In (forall_times n (ax_rep' (oc_form Q))) G) by (apply Hi; cbn; tauto).
  assert (Hfun : forall v d d', G ⊢C (oc_form Q)[v .: d .: sg] → (oc_form Q)[v .: d' .: sg] → d ≡' d').
  { intros v d d'. unfold oc_form. simp. fintro H1. fintro H2.
    fdestr H1 H1a H1c. fdestr H1a H1o H1q. fdestr H2 H2a H2c. fdestr H2a H2o H2q.
    fhave T : (ord_tri_g HG HR (in_tri1 _ HO) (in_tri2 _ HO) d d' H1o H2o). unfold Tri in T.
    fcases T Hl' H3; [fcases Hl' E1 E2|].
    - fabsurd. finst H2c d. fmp H2c E1. apply (IE H2c). fconv_goal (d .: v .: sg).
      fconv_in H1q (d .: v .: sg). exact H1q.
    - exact E2.
    - fabsurd. finst H1c d'. fmp H1c H3. apply (IE H1c). fconv_goal (d' .: v .: sg).
      fconv_in H2q (d' .: v .: sg). exact H2q. }
  pose proof (rep_use G n (oc_form Q) sg X Hr (fb_oc n Q Hfb) Hfun) as T. clear Hfun.
  fex T Y HY.
  fobtain (union_ex HG Y) as al Hal.
  fassert HYo : (∀ ($0 ∈' Y`[↑] → Ord0 $0)).
  { fall d. fintro Hd. pose proof HY as H. finst H d. fhave T : (iff_l _ _ _ H Hd). clear H.
    fex T v Hv. fdestr Hv Hv1 Hv2. unfold oc_form in Hv2. simp_in Hv2. fdestr Hv2 Hv2a Hv2c.
    fdestr Hv2a Hvo Hvq. exact Hvo. }
  fhave Halo : (ord_union_g HG Y al HYo (union0_of HG Y al Hal)).
  fexists al. fsplit; [exact Halo|].
  fall v. fintro Hv.
  finst Hall v. fmp Hall Hv. fex Hall d0 Hd0. fdestr Hd0 Hd0o Hd0q.
  fconv_in Hd0q (d0 .: v .: sg).
  fhave T : (least_ord_g HG HR (S n) Q (v .: sg) d0 Hfb Hl Hd0o Hd0q). fex T d Hd.
  fdestr Hd Hd12 Hd3. fdestr Hd12 Hdo Hdq.
  fconv_in Hdq (d .: v .: sg).
  fassert HdY : (d ∈' Y).
  { pose proof HY as H. finst H d. apply (iff_r _ _ _ H). clear H. fexists v. fsplit; [exact Hv|].
    unfold oc_form. simp. fsplit; [fsplit|].
    - exact Hdo.
    - fconv_goal (d .: v .: sg). exact Hdq.
    - fall g. fintro Hg. finst Hd3 g. fmp Hd3 Hg. fintro Hq. apply (IE Hd3).
      fconv_goal (g .: v .: sg). fconv_in Hq (g .: v .: sg). exact Hq. }
  fassert Hsub : (Sub0 d al).
  { unfold Sub0. fall z. fintro Hz. exact (union_in HG Y al d z Hal HdY Hz). }
  finst Hmono v d al. fmp Hmono Hdo. fmp Hmono Halo. fmp Hmono Hsub.
  rewrite ?subst_comp in Hmono. rewrite ?subst_comp.
  eapply fconv; [eapply IE; [exact Hmono|]|sub_eq].
  eapply fconv; [exact Hdq|sub_eq].
Qed.

Section Ord.
Context {G : list form} (HG : incl ZF0base G) (HR : In ax_reg' G) (HO : incl Ax_ord G).

(** ** Regularity *)
Lemma no_self x : G ⊢C x ∈' x -> G ⊢C ⊥.
Proof. exact (no_self_g HG HR x). Qed.
Lemma no_cycle2 x y : G ⊢C x ∈' y -> G ⊢C y ∈' x -> G ⊢C ⊥.
Proof. exact (no_cycle2_g HG HR x y). Qed.

(** ** Basic ordinal facts *)
Lemma ord_el a x : G ⊢C Ord0 a -> G ⊢C x ∈' a -> G ⊢C Ord0 x.
Proof. exact (ord_el_g a x). Qed.
Lemma ord_tr a x y : G ⊢C Ord0 a -> G ⊢C x ∈' y -> G ⊢C y ∈' a -> G ⊢C x ∈' a.
Proof. exact (ord_tr_g a x y). Qed.
Lemma ord_tri a b : G ⊢C Ord0 a -> G ⊢C Ord0 b -> G ⊢C a ∈' b ∨ a ≡' b ∨ b ∈' a.
Proof. exact (ord_tri_g HG HR (in_tri1 _ HO) (in_tri2 _ HO) a b). Qed.
Lemma ord_sub a b : G ⊢C Ord0 a -> G ⊢C Ord0 b -> G ⊢C Sub0 a b -> G ⊢C a ∈' b ∨ a ≡' b.
Proof. exact (ord_sub_g HG HR HO a b). Qed.
Lemma ord_el_sub a b : G ⊢C Ord0 b -> G ⊢C a ∈' b -> G ⊢C Sub0 a b.
Proof. exact (ord_el_sub_g a b). Qed.
Lemma ord_emp e : G ⊢C Emp0 e -> G ⊢C Ord0 e.
Proof. exact (ord_emp_g e). Qed.
Lemma ord_succ a s : G ⊢C Ord0 a -> G ⊢C Succ0 a s -> G ⊢C Ord0 s.
Proof. exact (ord_succ_g HG a s). Qed.
Lemma ord_succ_le a b s : G ⊢C Ord0 a -> G ⊢C Ord0 b -> G ⊢C a ∈' b -> G ⊢C Succ0 a s -> G ⊢C s ∈' b ∨ s ≡' b.
Proof. exact (ord_succ_le_g HG HR HO a b s). Qed.
Lemma ord_union X u : G ⊢C ∀ ($0 ∈' X`[↑] → Ord0 $0) -> G ⊢C Union0 X u -> G ⊢C Ord0 u.
Proof. exact (ord_union_g HG X u). Qed.
(** every ordinal is 0, a successor, or a limit *)
Lemma ord_cases a : G ⊢C Ord0 a -> G ⊢C Emp0 a ∨ (∃ (Ord0 $0 ∧ Succ0 $0 a`[↑])) ∨ Lim0 a.
Proof. exact (ord_cases_g HG HR HO a). Qed.
(** the successor of an element of a limit is in the limit *)
Lemma lim_succ l a s : G ⊢C Lim0 l -> G ⊢C a ∈' l -> G ⊢C Succ0 a s -> G ⊢C s ∈' l.
Proof. exact (lim_succ_g HG HR HO l a s). Qed.
(** for two ordinals there is an ordinal above both (their union) *)
Lemma ord_max a b : G ⊢C Ord0 a -> G ⊢C Ord0 b -> G ⊢C ∃ (Ord0 $0 ∧ Sub0 a`[↑] $0 ∧ Sub0 b`[↑] $0).
Proof. exact (ord_max_g HG a b). Qed.

(** ** ω *)
Lemma om_ex : In ax_om' G -> G ⊢C ∃ Om0 $0.
Proof. exact (om_ex_g HG HO). Qed.
Lemma om_unique w w' : G ⊢C Om0 w -> G ⊢C Om0 w' -> G ⊢C w ≡' w'.
Proof. exact (om_unique_g HG HR HO w w'). Qed.
Lemma om_ord w : G ⊢C Om0 w -> G ⊢C Ord0 w.
Proof. exact (om_ord_g w). Qed.
Lemma om_emp w e : G ⊢C Om0 w -> G ⊢C Emp0 e -> G ⊢C e ∈' w.
Proof. exact (om_emp_g HG HR w e). Qed.
Lemma om_succ w n s : G ⊢C Om0 w -> G ⊢C n ∈' w -> G ⊢C Succ0 n s -> G ⊢C s ∈' w.
Proof. intros H. unfold Om0 in H. exact (lim_succ_g HG HR HO w n s (CE1 H)). Qed.
(** induction over ω for a set X *)
Lemma om_ind w X : G ⊢C Om0 w -> G ⊢C ∀ (Emp0 $0 → $0 ∈' X`[↑]) ->
  G ⊢C ∀ ($0 ∈' w`[↑] → $0 ∈' X`[↑] → ∀ (Succ0 $1 $0 → $0 ∈' X`[↑]`[↑])) ->
  G ⊢C Sub0 w X.
Proof. exact (om_ind_g HG HR HO w X). Qed.
(** elements of ω are 0 or successors of elements of ω *)
Lemma om_el w n : G ⊢C Om0 w -> G ⊢C n ∈' w -> G ⊢C Emp0 n ∨ ∃ ($0 ∈' w`[↑] ∧ Succ0 $0 n`[↑]).
Proof. exact (om_el_g w n). Qed.

(** ** Schemas *)
(** least element: [psi] with $0 = the ordinal, $(k+1) = parameter [sg k] *)
Lemma least_ord n psi sg a : fb (S n) psi -> In (least_inst n psi) G ->
  G ⊢C Ord0 a -> G ⊢C psi[a .: sg] ->
  G ⊢C ∃ (Ord0 $0 ∧ psi[up sg] ∧ ∀ ($0 ∈' $1 → ¬ psi[up (sg >> subst_term ↑)])).
Proof. exact (least_ord_g HG HR n psi sg a). Qed.
(** transfinite induction *)
Lemma ord_ind n psi sg a : fb (S n) psi -> In (least_inst n (¬ psi)) G ->
  G ⊢C ∀ (Ord0 $0 → (∀ ($0 ∈' $1 → psi[up (sg >> subst_term ↑)])) → psi[up sg]) ->
  G ⊢C Ord0 a -> G ⊢C psi[a .: sg].
Proof. exact (ord_ind_g HG HR n psi sg a). Qed.
(** ordinal collection: [Q] with $0 = δ (an ordinal), $1 = v, $(k+2) = parameter [sg k];
    monotone in δ.  If every v ∈ X has some δ, one δ works for all of X. *)
Lemma ord_collect n Q sg X : fb (S (S n)) Q -> incl (oc_insts n Q) G ->
  G ⊢C ∀ ($0 ∈' X`[↑] → ∃ (Ord0 $0 ∧ Q[up (up sg)])) ->
  G ⊢C ∀ (∀ (∀ (Ord0 $1 → Ord0 $0 → Sub0 $1 $0 →
                Q[$1 .: $2 .: (fun k => (sg k)`[↑]`[↑]`[↑])] → Q[$0 .: $2 .: (fun k => (sg k)`[↑]`[↑]`[↑])]))) ->
  G ⊢C ∃ (Ord0 $0 ∧ ∀ ($0 ∈' X`[↑]`[↑] → Q[$1 .: $0 .: (fun k => (sg k)`[↑]`[↑])])).
Proof. exact (ord_collect_g HG HR HO n Q sg X). Qed.

End Ord.
