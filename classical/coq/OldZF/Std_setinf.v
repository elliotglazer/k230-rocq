(** * Std_setinf: O'Rear's (Zermelo) infinity [INF_lib] and von Neumann infinity [ax_om'] are
    interderivable over [ZF0] (closed separation / replacement instances), via the generic
    closure theorem of Std_setrec.

    [inf_or_to_zf]: from INF_lib at ∅ cut out Z, the least set containing ∅ and closed under
    singletons; (Z, ∅, x ↦ {x}) is an inductive structure; close {∅} under x ↦ x ∪ {x}
    (closure theorem) to get an inductive set W; ω := {u ∈ W | u is in every inductive set}.
    [inf_zf_to_or]: (ω, ∅, σ) is an inductive structure (σ is injective on ω because every
    natural number is transitive and not a member of itself); close {x} under singletons. *)
From Coq Require Import Arith Lia List.
From OldUndecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_setrec.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

(** ** Predicates *)
Definition SClos (T : term) : form := ∀ ($0 ∈' T`[↑] → ∃ ($0 ∈' T`[↑]`[↑] ∧ Sing $1 $0)).
Definition ZMem (u e : term) : form := ∀ ((e`[↑] ∈' $0 ∧ SClos $0) → u`[↑] ∈' $0).
Definition OmMem (u : term) : form := ∀ (is_inductive $0 → u`[↑] ∈' $0).
Definition Trans (n : term) : form := ∀ ∀ ($1 ∈' $0 → $0 ∈' n`[↑]`[↑] → $1 ∈' n`[↑]`[↑]).
Definition TNF (n : term) : form := Trans n ∧ ¬ (n ∈' n).
#[global] Arguments SClos : simpl never.
#[global] Arguments ZMem : simpl never.
#[global] Arguments OmMem : simpl never.
#[global] Arguments Trans : simpl never.
#[global] Arguments TNF : simpl never.

Lemma SClos_subst T sg : (SClos T)[sg] = SClos T`[sg].
Proof. psubst SClos. Qed.
#[global] Hint Rewrite SClos_subst : fsub.
Lemma ZMem_subst u e sg : (ZMem u e)[sg] = ZMem u`[sg] e`[sg].
Proof. psubst ZMem. Qed.
Lemma OmMem_subst u sg : (OmMem u)[sg] = OmMem u`[sg].
Proof. psubst OmMem. Qed.
Lemma Trans_subst u sg : (Trans u)[sg] = Trans u`[sg].
Proof. psubst Trans. Qed.
#[global] Hint Rewrite ZMem_subst OmMem_subst Trans_subst : fsub.
Lemma TNF_subst u sg : (TNF u)[sg] = TNF u`[sg].
Proof. psubst TNF. Qed.
#[global] Hint Rewrite TNF_subst : fsub.

Lemma INF_lib_eq : INF_lib = ∀ ∃ ($1 ∈' $0 ∧ SClos $0).
Proof. reflexivity. Qed.

Lemma ax_om'_eq : ax_om' = ∃ is_om $0.
Proof. reflexivity. Qed.

Definition zmem_form : form := ZMem $0 $1.
Definition ommem_form : form := OmMem $0.
Definition tnf_form : form := TNF $0.

Lemma fb_zmem : fb 2 zmem_form.
Proof. unfold zmem_form, ZMem, SClos, Sing. cbn. lia. Qed.
Lemma fb_ommem : fb 1 ommem_form.
Proof. unfold ommem_form, OmMem, is_inductive, is_eset, is_sigma. cbn. lia. Qed.
Lemma fb_tnf : fb 1 tnf_form.
Proof. unfold tnf_form, TNF, Trans. cbn. lia. Qed.

(** ** General facts *)
Lemma eset_unique {G} (HG : incl ZF0base G) e e' : G ⊢C is_eset e -> G ⊢C is_eset e' -> G ⊢C e ≡' e'.
Proof.
  intros H1 H2. apply (ext_rule HG); unfold sub'; fall z; fintro Hz; fabsurd.
  - exact (eset_el HG e z H1 Hz).
  - exact (eset_el HG e' z H2 Hz).
Qed.

Lemma Rel2_Sing x y : Rel2 (Sing $0 $1) x y = Sing x y.
Proof. unfold Rel2. now rewrite Sing_subst. Qed.
Lemma Rel2_sigma x y : Rel2 (is_sigma $0 $1) x y = is_sigma x y.
Proof. unfold Rel2. now rewrite is_sigma_subst. Qed.
#[global] Hint Rewrite Rel2_Sing Rel2_sigma : fsub.

Lemma ind_e {G} I : G ⊢C is_inductive I -> G ⊢C ∃ (is_eset $0 ∧ $0 ∈' I`[↑]).
Proof. intros H. exact (CE1 H). Qed.

Lemma ind_s {G} I u : G ⊢C is_inductive I -> G ⊢C u ∈' I -> G ⊢C ∃ (is_sigma u`[↑] $0 ∧ $0 ∈' I`[↑]).
Proof. intros H Hu. pose proof (CE2 H) as H2. finst H2 u. exact (IE H2 Hu). Qed.

(** ** INF_lib ⊢ ax_om' *)
Definition phSing : form := Sing $0 $1.
Definition phSig : form := is_sigma $0 $1.

Lemma or_to_zf_core {G} (HG : incl ZF0base G) (HI : incl (rec_insts phSing phSig) G)
  (HZ : In (forall_times 1 (ax_sep' zmem_form)) G) (HO : In (forall_times 0 (ax_sep' ommem_form)) G) :
  G ⊢C INF_lib -> G ⊢C ax_om'.
Proof.
  intros Hinf. rewrite INF_lib_eq in Hinf. rewrite ax_om'_eq.
  fobtain (eset_ex HG) as e He.
  finst Hinf e. fex Hinf Y HY. fdestr HY HeY HYc.
  pose proof (sep_use _ 1 zmem_form (e .: var) Y HZ fb_zmem) as T. unfold zmem_form in T. simp_in T.
  fex T Zs HZc.
  fassert HeZ : (e ∈' Zs).
  { pose proof HZc as H. finst H e. apply (iff_r _ _ _ H). fsplit; [exact HeY|].
    unfold ZMem. fall X. fintro HX. exact (CE1 HX). }
  fassert Htot : (STot phSing Zs).
  { unfold STot, phSing. fall z. fintro Hz. pose proof HZc as H. finst H z. fhave Hz' : (iff_l _ _ _ H Hz). clear H.
    fdestr Hz' HzY HzZ. pose proof HYc as H. unfold SClos in H. finst H z. fmp H HzY. fex H s Hs0. fdestr Hs0 HsY Hs.
    fexists s. fsplit; [exact Hs|]. pose proof HZc as H. finst H s. apply (iff_r _ _ _ H). clear H.
    fsplit; [exact HsY|]. unfold ZMem. fall X. fintro HX. pose proof HX as HX'. fdestr HX' HeX HXc.
    unfold ZMem in HzZ. finst HzZ X. fmp HzZ HX. unfold SClos in HXc. finst HXc z. fmp HXc HzZ.
    fex HXc s' Hs0'. fdestr Hs0' Hs'X Hs'. fhave E : (sing_unique HG z s s' Hs Hs'). fmem. }
  fassert Hinj : (SInj phSing Zs).
  { unfold SInj, phSing. fall z1. fall z2. fall z'. fintro H1. fintro H2. fintro H3. fintro H4.
    exact (sing_inj HG z1 z2 z' H3 H4). }
  fassert Hnz : (SNz phSing e Zs).
  { unfold SNz, phSing. fall z. fintro Hz. fintro Hs. exact (eset_el HG e z He (sing_in HG z e Hs)). }
  fassert Hind : (SInd phSing e Zs).
  { unfold SInd, phSing. fall X. fintro HeX. fintro Hcl. fall z. fintro Hz.
    pose proof HZc as H. finst H z. fhave Hz' : (CE2 (iff_l _ _ _ H Hz)). clear H.
    unfold ZMem in Hz'. finst Hz' X. apply (IE Hz'). fsplit; [exact HeX|].
    unfold SClos. fall w. fintro Hw. finst Hcl w. fmp Hcl Hw. fex Hcl s Hs. fdestr Hs Hs1 Hs2.
    fexists s. fsplit; assumption. }
  fassert Hgt : (GTot phSig).
  { unfold GTot, phSig. fall v. exact (succ_ex HG v). }
  fassert Hgf : (GFun phSig).
  { unfold GFun, phSig. fall v. fall w. fall w'. fintro H1. fintro H2. exact (succ_unique HG v w w' H1 H2). }
  fhave T : (closure_thm HG phSing phSig HI Zs e e HeZ Htot Hinj Hnz Hind Hgt Hgf).
  unfold phSig in T. simp_in T. fex T W HW. unfold Clos in HW. simp_in HW. fdestr HW HeW HWc.
  pose proof (sep_use _ 0 ommem_form var W HO fb_ommem) as T. unfold ommem_form in T. simp_in T.
  fex T Om HOc.
  fexists Om. unfold is_om. fsplit.
  - unfold is_inductive. fsplit.
    + fexists e. fsplit; [exact He|]. pose proof HOc as H. finst H e. apply (iff_r _ _ _ H). clear H.
      fsplit; [exact HeW|]. unfold OmMem. fall J. fintro HIi. fhave T : (ind_e J HIi). fex T e' He'.
      fdestr He' He'1 He'2. fhave E : (eset_unique HG e e' He He'1). fmem.
    + fall u. fintro Hu. pose proof HOc as H. finst H u. fhave Hu' : (iff_l _ _ _ H Hu). clear H.
      fdestr Hu' HuW HuO. pose proof HWc as H. finst H u. fmp H HuW. fex H s Hs0. fdestr Hs0 Hs HsW.
      fexists s. fsplit; [exact Hs|]. pose proof HOc as H. finst H s. apply (iff_r _ _ _ H). clear H.
      fsplit; [exact HsW|]. unfold OmMem. fall J. fintro HIi. unfold OmMem in HuO. finst HuO J. fmp HuO HIi.
      fhave T : (ind_s J u HIi HuO). fex T s' Hs'. fdestr Hs' Hs'1 Hs'2.
      fhave E : (succ_unique HG u s s' Hs Hs'1). fmem.
  - fall J. fintro HIi. unfold sub'. fall u. fintro Hu. pose proof HOc as H. finst H u.
    fhave Hu' : (CE2 (iff_l _ _ _ H Hu)). clear H. unfold OmMem in Hu'. finst Hu' J. exact (IE Hu' HIi).
Qed.

Lemma rec_insts_ZF0 phS phG psi : In psi (rec_insts phS phG) -> ZF0 psi.
Proof.
  intros [<-|[<-|[<-|[]]]].
  - apply ZF0_sep, sep_closed, fb_agr.
  - apply ZF0_sep, sep_closed, fb_exa.
  - apply ZF0_rep, rep_closed, fb_rr.
Qed.

Definition A_or_zf : list form :=
  ZF0base ++ rec_insts phSing phSig ++
  [forall_times 1 (ax_sep' zmem_form); forall_times 0 (ax_sep' ommem_form); INF_lib].

Theorem inf_or_to_zf : Inf_OR_to_ZF.
Proof.
  exists A_or_zf. split.
  - intros psi H. unfold A_or_zf in H. apply in_app_iff in H as [H|H]; [left; now apply ZF0_base|].
    apply in_app_iff in H as [H|H]; [left; eapply rec_insts_ZF0; exact H|].
    destruct H as [<-|[<-|[<-|[]]]].
    + left. apply ZF0_sep, sep_closed, fb_zmem.
    + left. apply ZF0_sep, sep_closed, fb_ommem.
    + now right.
  - assert (HG : incl ZF0base A_or_zf) by (intros x Hx; unfold A_or_zf; apply in_app_iff; now left).
    assert (HI : incl (rec_insts phSing phSig) A_or_zf)
      by (intros x Hx; unfold A_or_zf; apply in_app_iff; right; apply in_app_iff; now left).
    apply (or_to_zf_core HG HI).
    + unfold A_or_zf. apply in_app_iff; right; apply in_app_iff; right. cbn; tauto.
    + unfold A_or_zf. apply in_app_iff; right; apply in_app_iff; right. cbn; tauto.
    + apply Ctx. unfold A_or_zf. apply in_app_iff; right; apply in_app_iff; right. cbn; tauto.
Qed.


(** ** ax_om' ⊢ INF_lib *)
Lemma zf_to_or_core {G} (HG : incl ZF0base G) (HI : incl (rec_insts phSig phSing) G)
  (HT : In (forall_times 0 (ax_sep' tnf_form)) G) :
  G ⊢C ax_om' -> G ⊢C INF_lib.
Proof.
  intros Hom. rewrite ax_om'_eq in Hom. rewrite INF_lib_eq. fall x.
  fex Hom Om HOm. unfold is_om in HOm. fdestr HOm HInd HMin.
  fhave T : (ind_e Om HInd). fex T e He0. fdestr He0 He HeO.
  pose proof (sep_use _ 0 tnf_form var Om HT fb_tnf) as T. unfold tnf_form in T. simp_in T. fex T X HXc.
  fassert HXi : (is_inductive X).
  { unfold is_inductive. fsplit.
    - fexists e. fsplit; [exact He|]. pose proof HXc as H. finst H e. apply (iff_r _ _ _ H). clear H.
      fsplit; [exact HeO|]. unfold TNF. fsplit.
      + unfold Trans. fall y. fall m. fintro H1. fintro H2. fabsurd. exact (eset_el HG e m He H2).
      + fintro H. exact (eset_el HG e e He H).
    - fall u. fintro Hu. pose proof HXc as H. finst H u. fhave Hu' : (iff_l _ _ _ H Hu). clear H.
      fdestr Hu' HuO HuT. unfold TNF in HuT. fdestr HuT HuTr HuN.
      fhave T : (ind_s Om u HInd HuO). fex T s Hs0. fdestr Hs0 Hs HsO.
      fexists s. fsplit; [exact Hs|]. pose proof HXc as H. finst H s. apply (iff_r _ _ _ H). clear H.
      fsplit; [exact HsO|]. unfold TNF. fsplit.
      + unfold Trans. fall y. fall m. fintro Hym. fintro Hms.
        fhave T : (succ_el HG u s m Hs Hms). fcases T T1 T2.
        * apply (succ_in_l HG u s y Hs). unfold Trans in HuTr. finst HuTr y m. fmp HuTr Hym. fmp HuTr T1. exact HuTr.
        * apply (succ_in_l HG u s y Hs). fmem.
      + fintro Hss. fhave Hus : (succ_self HG u s Hs). fhave T : (succ_el HG u s s Hs Hss). fcases T T1 T2.
        * unfold Trans in HuTr. finst HuTr u s. fmp HuTr Hus. fmp HuTr T1. exact (IE HuN HuTr).
        * fassert Huu : (u ∈' u); [fmem|]. exact (IE HuN Huu). }
  fassert HOX : (∀ ($0 ∈' Om`[↑] → TNF $0)).
  { fall n. fintro Hn. pose proof HMin as H. finst H X. fmp H HXi. unfold sub' in H. finst H n. fmp H Hn.
    pose proof HXc as H'. finst H' n. exact (CE2 (iff_l _ _ _ H' H)). }
  fassert Htot : (STot phSig Om).
  { unfold STot, phSig. fall z. fintro Hz. exact (ind_s Om z HInd Hz). }
  fassert Hinj : (SInj phSig Om).
  { unfold SInj, phSig. fall z1. fall z2. fall z'. fintro H1. fintro H2. fintro H3. fintro H4.
    pose proof HOX as H. finst H z1. fmp H H1. unfold TNF in H. fdestr H Htr Hn.
    fhave Hz1 : (succ_self HG z1 z' H3). fhave Hz2 : (succ_self HG z2 z' H4).
    fhave T : (succ_el HG z2 z' z1 H4 Hz1). fcases T T1 T2.
    - fhave T : (succ_el HG z1 z' z2 H3 Hz2). fcases T T3 T4.
      + unfold Trans in Htr. finst Htr z1 z2. fmp Htr T1. fmp Htr T3. fabsurd. exact (IE Hn Htr).
      + feq.
    - exact T2. }
  fassert Hnz : (SNz phSig e Om).
  { unfold SNz, phSig. fall z. fintro Hz. fintro Hs. exact (eset_el HG e z He (succ_self HG z e Hs)). }
  fassert Hind : (SInd phSig e Om).
  { unfold SInd, phSig. fall Y. fintro HeY. fintro Hcl. fall z. fintro Hz.
    pose proof HMin as H. finst H Y. fassert HYi : (is_inductive Y).
    { unfold is_inductive. fsplit; [|exact Hcl]. fexists e. fsplit; [exact He|exact HeY]. }
    fmp H HYi. unfold sub' in H. finst H z. exact (IE H Hz). }
  fassert Hgt : (GTot phSing).
  { unfold GTot, phSing. fall v. exact (sing_ex HG v). }
  fassert Hgf : (GFun phSing).
  { unfold GFun, phSing. fall v. fall w. fall w'. fintro H1. fintro H2. exact (sing_unique HG v w w' H1 H2). }
  fhave T : (closure_thm HG phSig phSing HI Om e x HeO Htot Hinj Hnz Hind Hgt Hgf).
  unfold phSing in T. simp_in T. fex T Y HY. unfold Clos in HY. simp_in HY. fdestr HY HxY HYc.
  fexists Y. fsplit; [exact HxY|]. unfold SClos. fall u. fintro Hu. finst HYc u. fmp HYc Hu.
  fex HYc w Hw. fdestr Hw Hw1 Hw2. fexists w. fsplit; assumption.
Qed.

Definition A_zf_or : list form :=
  ZF0base ++ rec_insts phSig phSing ++ [forall_times 0 (ax_sep' tnf_form); ax_om'].

Theorem inf_zf_to_or : Inf_ZF_to_OR.
Proof.
  exists A_zf_or. split.
  - intros psi H. unfold A_zf_or in H. apply in_app_iff in H as [H|H]; [left; now apply ZF0_base|].
    apply in_app_iff in H as [H|H]; [left; eapply rec_insts_ZF0; exact H|].
    destruct H as [<-|[<-|[]]].
    + left. apply ZF0_sep, sep_closed, fb_tnf.
    + now right.
  - assert (HG : incl ZF0base A_zf_or) by (intros x Hx; unfold A_zf_or; apply in_app_iff; now left).
    assert (HI : incl (rec_insts phSig phSing) A_zf_or)
      by (intros x Hx; unfold A_zf_or; apply in_app_iff; right; apply in_app_iff; now left).
    apply (zf_to_or_core HG HI).
    + unfold A_zf_or. apply in_app_iff; right; apply in_app_iff; right. cbn; tauto.
    + apply Ctx. unfold A_zf_or. apply in_app_iff; right; apply in_app_iff; right. cbn; tauto.
Qed.
