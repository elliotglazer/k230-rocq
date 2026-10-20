(** Fixed omega recursion-domain laws, extracted from the pinned closure_om
    prelude. There is no varying relation matrix in this finite certificate. *)
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_iface Std_setnd Std_setbase Std_setinf.
From OldZF Require Std_setrec.
From OldZFC Require Import Z_rel Z_base Z_prim Z_ord Z_trec Z_cl Z_L Z_refl.
From PAModel Require Import SourceLFixed SourceLNonempty SourceHierarchyOld.
From Stdlib Require Import Lists.List.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.
Definition old_omega_recursion_body :form:=($0 ∈' $1 ∧
  (Std_setrec.STot phSig $1 ∧(Std_setrec.SInj phSig $1 ∧
    (Std_setrec.SNz phSig $0 $1 ∧Std_setrec.SInd phSig $0 $1)))).
Definition old_omega_recursion_inner :form:=∃old_omega_recursion_body.
Definition old_omega_recursion_structure :form:=∃old_omega_recursion_inner.

Theorem old_omega_recursion_structure_general {G}(HG:incl ZF0base G)
  (HT:In sepTnf G)(HOm:In ax_om' G):G ⊢C old_omega_recursion_structure.
Proof.
  assert (Hom : G ⊢C ax_om') by (apply Ctx; exact HOm).
  rewrite ax_om'_eq in Hom.
  fex Hom Om HOm'. unfold is_om in HOm'. fdestr HOm' HInd HMin.
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
  fassert Htot : (Std_setrec.STot phSig Om).
  { unfold Std_setrec.STot, phSig. fall z. fintro Hz. exact (ind_s Om z HInd Hz). }
  fassert Hinj : (Std_setrec.SInj phSig Om).
  { unfold Std_setrec.SInj, phSig. fall z1. fall z2. fall z'. fintro H1. fintro H2. fintro H3. fintro H4.
    pose proof HOX as H. finst H z1. fmp H H1. unfold TNF in H. fdestr H Htr Hn.
    fhave Hz1 : (succ_self HG z1 z' H3). fhave Hz2 : (succ_self HG z2 z' H4).
    fhave T : (succ_el HG z2 z' z1 H4 Hz1). fcases T T1 T2.
    - fhave T : (succ_el HG z1 z' z2 H3 Hz2). fcases T T3 T4.
      + unfold Trans in Htr. finst Htr z1 z2. fmp Htr T1. fmp Htr T3. fabsurd. exact (IE Hn Htr).
      + feq.
    - exact T2. }
  fassert Hnz : (Std_setrec.SNz phSig e Om).
  { unfold Std_setrec.SNz, phSig. fall z. fintro Hz. fintro Hs. exact (eset_el HG e z He (succ_self HG z e Hs)). }
  fassert Hind : (Std_setrec.SInd phSig e Om).
  { unfold Std_setrec.SInd, phSig. fall Y. fintro HeY. fintro Hcl. fall z. fintro Hz.
    pose proof HMin as H. finst H Y. fassert HYi : (is_inductive Y).
    { unfold is_inductive. fsplit; [|exact Hcl]. fexists e. fsplit; [exact He|exact HeY]. }
    fmp H HYi. unfold sub' in H. finst H z. exact (IE H Hz). }
  unfold old_omega_recursion_structure,old_omega_recursion_inner,old_omega_recursion_body. fexists Om. fexists e.
  fsplit;[exact HeO|]. fsplit;[exact Htot|]. fsplit;[exact Hinj|]. fsplit;assumption.
Qed.

Definition old_omega_recursion_background:=sepTnf::old_L_background.
Theorem old_omega_recursion_background_valid a:In a old_omega_recursion_background ->ZFR a.
Proof.
  intros[<-|HA].
  - unfold sepTnf. apply ZFR_sep. exact fb_tnf.
  - exact(old_L_background_valid a HA).
Qed.
Theorem old_omega_recursion_structure_proof:old_omega_recursion_background ⊢C old_omega_recursion_structure.
Proof.
  apply old_omega_recursion_structure_general.
  - intros a HA. right. exact(old_hierarchy_base a HA).
  - now left.
  - right. exact old_hierarchy_omega.
Qed.
Print Assumptions old_omega_recursion_structure_general.
Print Assumptions old_omega_recursion_structure_proof.
