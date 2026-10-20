(** * Std_setrec: a generic recursion / closure theorem (ND derivations, minimal signature).

    Data: a set [N], an element [o], and two arbitrary formulas [phS], [phG] read as binary
    relations via [Rel2] ([Rel2 phi x y := phi[x .: y .: (fun _ => x)]], so substitution commutes
    with [Rel2] for every formula and no free-variable side conditions arise).

    If (N, o, S) is an "inductive structure" ([o ∈ N]; S total on N into N; S injective on N;
    o not an S-successor of an element of N; induction over subsets: every set containing o and
    closed under S-successors contains N) and G is a total functional relation, then for every
    [a] there is a set containing [a] and closed under G ([closure_thm]).

    Proof: attempts [f] (sets of ordered pairs with f(o) = a and f(S u) = G(f u) wherever
    defined, read relationally) agree on N (induction); every [z ∈ N] is in the domain of an
    attempt (induction, extending by one pair); the image of N under "some attempt maps z to v"
    (replacement) is the required set.

    Uses the instances [rec_insts phS phG] (two separations, one replacement). *)
From Coq Require Import Arith Lia List.
From OldUndecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

(** ** Binary relations given by formulas *)
Definition Rel2 (phi : form) (x y : term) : form := phi[x .: y .: (fun _ => x)].
#[global] Arguments Rel2 : simpl never.

Lemma Rel2_subst phi x y sg : (Rel2 phi x y)[sg] = Rel2 phi x`[sg] y`[sg].
Proof. unfold Rel2. rewrite subst_comp. apply subst_ext. intros [|[|n]]; reflexivity. Qed.
#[global] Hint Rewrite Rel2_subst : fsub.

Lemma fb_Rel2 phi x y N : idx x < N -> idx y < N -> fb N (Rel2 phi x y).
Proof.
  intros Hx Hy. destruct (fb_exists phi) as [M HM]. unfold Rel2. eapply fb_subst; [exact HM|].
  intros [|[|i]] _; cbn; assumption.
Qed.

(** ** The predicates of the construction *)
Definition Att (phS phG : form) (o a N f : term) : form :=
  (∀ (App f`[↑] o`[↑] $0 → $0 ≡' a`[↑])) ∧
  (∀ ∀ ∀ ($2 ∈' N`[↑]`[↑]`[↑] → Rel2 phS $2 $1 → App f`[↑]`[↑]`[↑] $1 $0 →
          ∃ (App f`[↑]`[↑]`[↑]`[↑] $3 $0 ∧ Rel2 phG $0 $1))).
Definition Agr (f g z : term) : form :=
  ∀ ∀ (App f`[↑]`[↑] z`[↑]`[↑] $1 → App g`[↑]`[↑] z`[↑]`[↑] $0 → $1 ≡' $0).
Definition ExA (phS phG : form) (z o a N : term) : form :=
  ∃ (Att phS phG o`[↑] a`[↑] N`[↑] $0 ∧ ∃ App $1 z`[↑]`[↑] $0).
Definition RR (phS phG : form) (z v o a N : term) : form :=
  z ∈' N ∧ ∃ (Att phS phG o`[↑] a`[↑] N`[↑] $0 ∧ App $0 z`[↑] v`[↑]).
#[global] Arguments Att : simpl never.
#[global] Arguments Agr : simpl never.
#[global] Arguments ExA : simpl never.
#[global] Arguments RR : simpl never.

Lemma Att_subst phS phG o a N f sg : (Att phS phG o a N f)[sg] = Att phS phG o`[sg] a`[sg] N`[sg] f`[sg].
Proof. psubst Att. Qed.
Lemma Agr_subst f g z sg : (Agr f g z)[sg] = Agr f`[sg] g`[sg] z`[sg].
Proof. psubst Agr. Qed.
#[global] Hint Rewrite Att_subst Agr_subst : fsub.
Lemma ExA_subst phS phG z o a N sg : (ExA phS phG z o a N)[sg] = ExA phS phG z`[sg] o`[sg] a`[sg] N`[sg].
Proof. psubst ExA. Qed.
Lemma RR_subst phS phG z v o a N sg : (RR phS phG z v o a N)[sg] = RR phS phG z`[sg] v`[sg] o`[sg] a`[sg] N`[sg].
Proof. psubst RR. Qed.
#[global] Hint Rewrite ExA_subst RR_subst : fsub.

(** the separation / replacement formulas and instances *)
Definition agr_form : form := Agr $1 $2 $0.
Definition exa_form (phS phG : form) : form := ExA phS phG $0 $1 $2 $3.
Definition rr_form (phS phG : form) : form := RR phS phG $0 $1 $2 $3 $4.

Definition rec_insts (phS phG : form) : list form :=
  [forall_times 2 (ax_sep' agr_form); forall_times 3 (ax_sep' (exa_form phS phG));
   forall_times 3 (ax_rep' (rr_form phS phG))].

Ltac fbsolve :=
  unfold agr_form, exa_form, rr_form, RR, ExA, Agr, Att, App, OP, Sing, is_pair;
  cbn; repeat match goal with
              | |- _ /\ _ => split
              | |- fb _ (Rel2 _ _ _) => apply fb_Rel2; cbn; lia
              | |- _ < _ => lia
              | |- True => exact I
              end.

Lemma fb_agr : fb 3 agr_form.
Proof. fbsolve. Qed.
Lemma fb_exa phS phG : fb 4 (exa_form phS phG).
Proof. fbsolve. Qed.
Lemma fb_rr phS phG : fb 5 (rr_form phS phG).
Proof. fbsolve. Qed.

Lemma rec_insts_closed phS phG psi : In psi (rec_insts phS phG) -> closedf psi.
Proof.
  intros [<-|[<-|[<-|[]]]].
  - apply sep_closed, fb_agr.
  - apply sep_closed, fb_exa.
  - apply rep_closed, fb_rr.
Qed.

Section Inst.
Context {G : list form} {phS phG : form} (HI : incl (rec_insts phS phG) G).
Lemma in_agr : In (forall_times 2 (ax_sep' agr_form)) G.
Proof. apply HI. cbn; tauto. Qed.
Lemma in_exa : In (forall_times 3 (ax_sep' (exa_form phS phG))) G.
Proof. apply HI. cbn; tauto. Qed.
Lemma in_rr : In (forall_times 3 (ax_rep' (rr_form phS phG))) G.
Proof. apply HI. cbn; tauto. Qed.
End Inst.

(** ** Hypotheses of the closure theorem *)
Definition STot (phS : form) (N : term) : form := ∀ ($0 ∈' N`[↑] → ∃ (Rel2 phS $1 $0 ∧ $0 ∈' N`[↑]`[↑])).
Definition SInj (phS : form) (N : term) : form :=
  ∀ ∀ ∀ ($2 ∈' N`[↑]`[↑]`[↑] → $1 ∈' N`[↑]`[↑]`[↑] → Rel2 phS $2 $0 → Rel2 phS $1 $0 → $2 ≡' $1).
Definition SNz (phS : form) (o N : term) : form := ∀ ($0 ∈' N`[↑] → ¬ Rel2 phS $0 o`[↑]).
Definition SInd (phS : form) (o N : term) : form :=
  ∀ (o`[↑] ∈' $0 → (∀ ($0 ∈' $1 → ∃ (Rel2 phS $1 $0 ∧ $0 ∈' $2))) → ∀ ($0 ∈' N`[↑]`[↑] → $0 ∈' $1)).
Definition GTot (phG : form) : form := ∀ ∃ Rel2 phG $1 $0.
Definition GFun (phG : form) : form := ∀ ∀ ∀ (Rel2 phG $2 $1 → Rel2 phG $2 $0 → $1 ≡' $0).
Definition Clos (phG : form) (a Y : term) : form := a ∈' Y ∧ ∀ ($0 ∈' Y`[↑] → ∃ (Rel2 phG $1 $0 ∧ $0 ∈' Y`[↑]`[↑])).
#[global] Arguments STot : simpl never.
#[global] Arguments SInj : simpl never.
#[global] Arguments SNz : simpl never.
#[global] Arguments SInd : simpl never.
#[global] Arguments GTot : simpl never.
#[global] Arguments GFun : simpl never.
#[global] Arguments Clos : simpl never.

Lemma STot_subst phS N sg : (STot phS N)[sg] = STot phS N`[sg].
Proof. psubst STot. Qed.
Lemma SInj_subst phS N sg : (SInj phS N)[sg] = SInj phS N`[sg].
Proof. psubst SInj. Qed.
Lemma SNz_subst phS o N sg : (SNz phS o N)[sg] = SNz phS o`[sg] N`[sg].
Proof. psubst SNz. Qed.
Lemma SInd_subst phS o N sg : (SInd phS o N)[sg] = SInd phS o`[sg] N`[sg].
Proof. psubst SInd. Qed.
Lemma GTot_subst phG sg : (GTot phG)[sg] = GTot phG.
Proof. psubst GTot. Qed.
Lemma GFun_subst phG sg : (GFun phG)[sg] = GFun phG.
Proof. psubst GFun. Qed.
Lemma Clos_subst phG a Y sg : (Clos phG a Y)[sg] = Clos phG a`[sg] Y`[sg].
Proof. psubst Clos. Qed.
#[global] Hint Rewrite STot_subst SInj_subst SNz_subst SInd_subst GTot_subst GFun_subst Clos_subst : fsub.

(** ** Accessors *)
Section Access.
Context {G : list form} (HG : incl ZF0base G) (phS phG : form).

Lemma att_o o a N f v : G ⊢C Att phS phG o a N f -> G ⊢C App f o v -> G ⊢C v ≡' a.
Proof. intros H Hv. pose proof (CE1 H) as H1. finst H1 v. exact (IE H1 Hv). Qed.

Lemma att_s o a N f u u' v' : G ⊢C Att phS phG o a N f -> G ⊢C u ∈' N -> G ⊢C Rel2 phS u u' ->
  G ⊢C App f u' v' -> G ⊢C ∃ (App f`[↑] u`[↑] $0 ∧ Rel2 phG $0 v'`[↑]).
Proof.
  intros H Hu Huu' Hv. pose proof (CE2 H) as H2. finst H2 u u' v'.
  fmp H2 Hu. fmp H2 Huu'. fmp H2 Hv. exact H2.
Qed.

Lemma stot_use N z : G ⊢C STot phS N -> G ⊢C z ∈' N -> G ⊢C ∃ (Rel2 phS z`[↑] $0 ∧ $0 ∈' N`[↑]).
Proof. intros H Hz. unfold STot in H. finst H z. exact (IE H Hz). Qed.

Lemma sinj_use N z1 z2 z' : G ⊢C SInj phS N -> G ⊢C z1 ∈' N -> G ⊢C z2 ∈' N ->
  G ⊢C Rel2 phS z1 z' -> G ⊢C Rel2 phS z2 z' -> G ⊢C z1 ≡' z2.
Proof. intros H H1 H2 H3 H4. unfold SInj in H. finst H z1 z2 z'. exact (IE (IE (IE (IE H H1) H2) H3) H4). Qed.

Lemma snz_use o N z : G ⊢C SNz phS o N -> G ⊢C z ∈' N -> G ⊢C Rel2 phS z o -> G ⊢C ⊥.
Proof. intros H H1 H2. unfold SNz in H. finst H z. exact (IE (IE H H1) H2). Qed.

Lemma gtot_use v : G ⊢C GTot phG -> G ⊢C ∃ Rel2 phG v`[↑] $0.
Proof. intros H. unfold GTot in H. finst H v. exact H. Qed.

Lemma gfun_use v w w' : G ⊢C GFun phG -> G ⊢C Rel2 phG v w -> G ⊢C Rel2 phG v w' -> G ⊢C w ≡' w'.
Proof. intros H H1 H2. unfold GFun in H. finst H v w w'. exact (IE (IE H H1) H2). Qed.

Lemma sind_use o N X : G ⊢C SInd phS o N -> G ⊢C o ∈' X ->
  G ⊢C ∀ ($0 ∈' X`[↑] → ∃ (Rel2 phS $1 $0 ∧ $0 ∈' X`[↑]`[↑])) -> G ⊢C ∀ ($0 ∈' N`[↑] → $0 ∈' X`[↑]).
Proof. intros H H1 H2. unfold SInd in H. finst H X. exact (IE (IE H H1) H2). Qed.

End Access.

(** ** Attempts agree on N *)
Lemma agree_lemma {G} (HG : incl ZF0base G) phS phG (HI : incl (rec_insts phS phG) G) N o a f g :
  G ⊢C o ∈' N -> G ⊢C STot phS N -> G ⊢C SInd phS o N -> G ⊢C GFun phG ->
  G ⊢C Att phS phG o a N f -> G ⊢C Att phS phG o a N g ->
  G ⊢C ∀ ($0 ∈' N`[↑] → Agr f`[↑] g`[↑] $0).
Proof.
  intros Ho Htot Hind Hfun Hf Hg.
  pose proof (sep_use G 2 agr_form (f .: g .: var) N (in_agr HI) fb_agr) as HX.
  unfold agr_form in HX. simp_in HX. fex HX X HXc.
  fassert H0 : (o ∈' X).
  { pose proof HXc as H. finst H o. apply (iff_r _ _ _ H). fsplit; [exact Ho|].
    unfold Agr. fall v1. fall v2. fintro A1. fintro A2.
    fhave E1 : (att_o phS phG o a N f v1 Hf A1). fhave E2 : (att_o phS phG o a N g v2 Hg A2). feq. }
  fassert H1 : (∀ ($0 ∈' X`[↑] → ∃ (Rel2 phS $1 $0 ∧ $0 ∈' X`[↑]`[↑]))).
  { fall z. fintro Hz. pose proof HXc as H. finst H z. fhave Hz' : (iff_l _ _ _ H Hz). clear H.
    fdestr Hz' HzN HzA. fhave T : (stot_use phS N z Htot HzN). fex T z' Hz'. fdestr Hz' Hs Hz'N.
    fexists z'. fsplit; [exact Hs|]. pose proof HXc as H. finst H z'. apply (iff_r _ _ _ H). clear H.
    fsplit; [exact Hz'N|]. unfold Agr. fall v1. fall v2. fintro A1. fintro A2.
    fhave T : (att_s phS phG o a N f z z' v1 Hf HzN Hs A1). fex T u1 Hu1. fdestr Hu1 Au1 Gu1.
    fhave T : (att_s phS phG o a N g z z' v2 Hg HzN Hs A2). fex T u2 Hu2. fdestr Hu2 Au2 Gu2.
    unfold Agr in HzA. finst HzA u1 u2. fmp HzA Au1. fmp HzA Au2.
    frew_in HzA (Rel2 phG $0 v2`[↑]) Gu2.
    exact (gfun_use phG u1 v1 v2 Hfun Gu1 Gu2). }
  fhave HN : (sind_use phS o N X Hind H0 H1).
  fall z. fintro Hz. finst HN z. fmp HN Hz. pose proof HXc as H. finst H z.
  exact (CE2 (iff_l _ _ _ H HN)).
Qed.

Lemma agree_use {G} (HG : incl ZF0base G) f g z v1 v2 :
  G ⊢C Agr f g z -> G ⊢C App f z v1 -> G ⊢C App g z v2 -> G ⊢C v1 ≡' v2.
Proof. intros H H1 H2. unfold Agr in H. finst H v1 v2. exact (IE (IE H H1) H2). Qed.

(** ** The one-point attempt {(o, a)} *)
Lemma att_base {G} (HG : incl ZF0base G) phS phG N o a :
  G ⊢C SNz phS o N -> G ⊢C ∃ (Att phS phG o`[↑] a`[↑] N`[↑] $0 ∧ App $0 o`[↑] a`[↑]).
Proof.
  intros Hnz. fobtain (op_ex HG o a) as q Hq. fobtain (sing_ex HG q) as f Hf. fexists f. fsplit.
  - unfold Att. fsplit.
    + fall v. fintro Hv. fhave H : (app_sing HG q f o v Hf Hv).
      exact (CE2 (op_inj HG o v o a q q H Hq (eq_refl' HG q))).
    + fall u. fall u'. fall v'. fintro Hu. fintro Hs. fintro Hv.
      fhave H : (app_sing HG q f u' v' Hf Hv). fhave E : (op_inj HG u' v' o a q q H Hq (eq_refl' HG q)).
      fdestr E E1 E2. frew_in E1 (Rel2 phS u`[↑] $0) Hs. fabsurd. exact (snz_use phS o N u Hnz Hu Hs).
  - exact (app_sing_intro HG q f o a Hf Hq).
Qed.

(** ** Every element of N is in the domain of an attempt *)
Lemma exist_lemma {G} (HG : incl ZF0base G) phS phG (HI : incl (rec_insts phS phG) G) N o a :
  G ⊢C o ∈' N -> G ⊢C STot phS N -> G ⊢C SInj phS N -> G ⊢C SNz phS o N -> G ⊢C SInd phS o N ->
  G ⊢C GTot phG ->
  G ⊢C ∀ ($0 ∈' N`[↑] → ExA phS phG $0 o`[↑] a`[↑] N`[↑]).
Proof.
  intros Ho Htot Hinj Hnz Hind Htotg.
  pose proof (sep_use G 3 (exa_form phS phG) (o .: a .: N .: var) N (in_exa HI) (fb_exa phS phG)) as HX.
  unfold exa_form in HX. simp_in HX. fex HX X HXc.
  fassert H0 : (o ∈' X).
  { pose proof HXc as H. finst H o. apply (iff_r _ _ _ H). fsplit; [exact Ho|].
    fhave T : (att_base HG phS phG N o a Hnz). fex T f Hf. fdestr Hf Hf1 Hf2.
    unfold ExA. fexists f. fsplit; [exact Hf1|]. fexists a. exact Hf2. }
  fassert H1 : (∀ ($0 ∈' X`[↑] → ∃ (Rel2 phS $1 $0 ∧ $0 ∈' X`[↑]`[↑]))).
  { fall z. fintro Hz. pose proof HXc as H. finst H z. fhave Hz' : (iff_l _ _ _ H Hz). clear H.
    fdestr Hz' HzN HzE. fhave T : (stot_use phS N z Htot HzN). fex T z' Hz'. fdestr Hz' Hs Hz'N.
    fexists z'. fsplit; [exact Hs|]. pose proof HXc as H. finst H z'. apply (iff_r _ _ _ H). clear H.
    fsplit; [exact Hz'N|].
    unfold ExA in HzE. fex HzE f Hf. fdestr Hf Hfa Hfz. fex Hfz v Hv.
    fhave T : (gtot_use phG v Htotg). fex T w Hw.
    fobtain (op_ex HG z' w) as q Hq. fobtain (adj_ex HG f q) as g Hg.
    unfold ExA. fexists g. fsplit.
    - unfold Att. fsplit.
      + fall v0. fintro Hv0. fhave T : (app_adj_el HG f q g o v0 Hg Hv0). fcases T T1 T2.
        * exact (att_o phS phG o a N f v0 Hfa T1).
        * fhave E : (op_inj HG o v0 z' w q q T2 Hq (eq_refl' HG q)). fdestr E E1 E2.
          frew_in E1 (Rel2 phS z`[↑] $0) Hs. fabsurd. exact (snz_use phS o N z Hnz HzN Hs).
      + fall u. fall u'. fall v'. fintro Hu. fintro Hs'. fintro Hv'.
        fhave T : (app_adj_el HG f q g u' v' Hg Hv'). fcases T T1 T2.
        * fhave T : (att_s phS phG o a N f u u' v' Hfa Hu Hs' T1). fex T v1 Hv1. fdestr Hv1 Hv1a Hv1b.
          fexists v1. fsplit; [exact (app_adj_l HG f q g u v1 Hg Hv1a)|exact Hv1b].
        * fhave E : (op_inj HG u' v' z' w q q T2 Hq (eq_refl' HG q)). fdestr E E1 E2.
          frew_in E1 (Rel2 phS u`[↑] $0) Hs'.
          fhave Euz : (sinj_use phS N u z z' Hinj Hu HzN Hs' Hs).
          fexists v. fsplit.
          -- apply (app_adj_l HG f q g u v Hg). frew Euz (App f`[↑] $0 v`[↑]). exact Hv.
          -- frew E2 (Rel2 phG v`[↑] $0). exact Hw.
    - fexists w. exact (app_adj_r HG f q g z' w Hg Hq). }
  fhave HN : (sind_use phS o N X Hind H0 H1).
  fall z. fintro Hz. finst HN z. fmp HN Hz. pose proof HXc as H. finst H z.
  exact (CE2 (iff_l _ _ _ H HN)).
Qed.

(** ** The closure theorem *)
Theorem closure_thm {G} (HG : incl ZF0base G) phS phG (HI : incl (rec_insts phS phG) G) N o a :
  G ⊢C o ∈' N -> G ⊢C STot phS N -> G ⊢C SInj phS N -> G ⊢C SNz phS o N -> G ⊢C SInd phS o N ->
  G ⊢C GTot phG -> G ⊢C GFun phG ->
  G ⊢C ∃ Clos phG a`[↑] $0.
Proof.
  intros Ho Htot Hinj Hnz Hind Htotg Hfun.
  pose proof (rep_use G 3 (rr_form phS phG) (o .: a .: N .: var) N (in_rr HI) (fb_rr phS phG)) as HY.
  unfold rr_form in HY. simp_in HY.
  assert (HY' : G ⊢C ∃ (∀ $0 ∈' $1 ↔ (∃ $0 ∈' N`[↑]`[↑]`[↑] ∧ RR phS phG $0 $1 o`[↑]`[↑]`[↑] a`[↑]`[↑]`[↑] N`[↑]`[↑]`[↑]))).
  { apply HY. intros z b b'. simp. fintro R1. fintro R2. unfold RR in R1, R2.
    fdestr R1 HzN R1'. fdestr R2 HzN' R2'. fex R1' f Hf. fdestr Hf Hfa Hfz. fex R2' g Hg. fdestr Hg Hga Hgz.
    fhave HA : (agree_lemma HG phS phG HI N o a f g Ho Htot Hind Hfun Hfa Hga). finst HA z. fmp HA HzN.
    exact (agree_use HG f g z b b' HA Hfz Hgz). }
  clear HY. fex HY' Y HYc. fexists Y. unfold Clos. fsplit.
  - pose proof HYc as H. finst H a. apply (iff_r _ _ _ H). fexists o. fsplit; [exact Ho|].
    unfold RR. fsplit; [exact Ho|]. exact (att_base HG phS phG N o a Hnz).
  - fall v. fintro Hv. pose proof HYc as H. finst H v. fhave T : (iff_l _ _ _ H Hv). clear H.
    fex T z Hz. fdestr Hz HzN HzR. unfold RR in HzR. fdestr HzR HzN' HzR'. fex HzR' f Hf. fdestr Hf Hfa Hfz.
    fhave T : (stot_use phS N z Htot HzN). fex T z' Hz'. fdestr Hz' Hs Hz'N.
    fhave HE : (exist_lemma HG phS phG HI N o a Ho Htot Hinj Hnz Hind Htotg). finst HE z'. fmp HE Hz'N.
    unfold ExA in HE. fex HE g Hg. fdestr Hg Hga Hgz'. fex Hgz' w Hw.
    fhave T : (att_s phS phG o a N g z z' w Hga HzN Hs Hw). fex T u1 Hu1. fdestr Hu1 Hu1a Hu1b.
    fhave HA : (agree_lemma HG phS phG HI N o a f g Ho Htot Hind Hfun Hfa Hga). finst HA z. fmp HA HzN.
    fhave E : (agree_use HG f g z v u1 HA Hfz Hu1a).
    fexists w. fsplit.
    + frew_in E (Rel2 phG $0 w`[↑]) Hu1b. exact Hu1b.
    + pose proof HYc as H. finst H w. apply (iff_r _ _ _ H). fexists z'. fsplit; [exact Hz'N|].
      unfold RR. fsplit; [exact Hz'N|]. fexists g. fsplit; [exact Hga|exact Hw].
Qed.
