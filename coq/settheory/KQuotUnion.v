(** Union of two supported families of bisimulations, with a new root edge. *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_F Std_breq.
From ZFC Require Import Z_base.
From K230S Require Import KP0 KP0Use KPRaw KPPair KPTransitive KBase KMarkers KTagged KRelation KQuot KQuotSym KQuotCollect.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Definition family_member (t cf cb r : term) : form := t ∈' r ∧ (r ∈' cf ∨ r ∈' cb).
Definition family_edge (t cf cb x y : term) : form :=
  ∃ (family_member t`[↑] cf`[↑] cb`[↑] $0 ∧ App0 $0 x`[↑] y`[↑]).
#[global] Arguments family_member : simpl never.
#[global] Arguments family_edge : simpl never.
Lemma family_member_subst t cf cb r sg :
  (family_member t cf cb r)[sg] = family_member t`[sg] cf`[sg] cb`[sg] r`[sg].
Proof. psubst family_member. Qed.
#[global] Hint Rewrite family_member_subst : fsub.
Lemma family_edge_subst t cf cb x y sg :
  (family_edge t cf cb x y)[sg] = family_edge t`[sg] cf`[sg] cb`[sg] x`[sg] y`[sg].
Proof. psubst family_edge. Qed.
#[global] Hint Rewrite family_edge_subst : fsub.

Lemma family_member_bisim G t cf cb r :
  G ⊢C bisim_family t cf -> G ⊢C bisim_family t cb ->
  G ⊢C family_member t cf cb r -> G ⊢C dbisim t r.
Proof.
  intros HF HB HM. unfold family_member in HM. fdestr HM Htr Hcases.
  fcases Hcases Hrf Hrb.
  - unfold bisim_family in HF. finst HF r. apply (IE HF). unfold dchild. fsplit; assumption.
  - unfold bisim_family in HB. finst HB r. apply (IE HB). unfold dchild. fsplit; assumption.
Qed.

Lemma family_edge_bounds G t cf cb v x y :
  G ⊢C raw_transitive v -> G ⊢C cf ∈' v -> G ⊢C cb ∈' v ->
  G ⊢C family_edge t cf cb x y -> G ⊢C x ∈' v ∧ y ∈' v.
Proof.
  intros Htrans Hcf Hcb Hxy. unfold family_edge in Hxy. fex Hxy r HR.
  fdestr HR HM Hedge. unfold family_member in HM. pose proof (CE2 HM) as Hcases.
  fassert HrV : (r ∈' v).
  { fcases Hcases Hrf Hrb.
    - exact (raw_transitive_element _ v cf r Htrans Hcf Hrf).
    - exact (raw_transitive_element _ v cb r Htrans Hcb Hrb). }
  exact (raw_app_endpoints _ v r x y Htrans HrV Hedge).
Qed.

Lemma family_edge_types G t cf cb x y :
  G ⊢C bisim_family t cf -> G ⊢C bisim_family t cb ->
  G ⊢C family_edge t cf cb x y -> G ⊢C t ∈' x ∧ t ∈' y.
Proof.
  intros HF HB Hxy. unfold family_edge in Hxy. fex Hxy r HR. fdestr HR HM Hedge.
  pose proof (family_member_bisim _ t cf cb r HF HB HM) as Hbis.
  exact (dbisim_types _ t r x y Hbis Hedge).
Qed.

Lemma family_edge_forth G t cf cb p q a :
  G ⊢C bisim_family t cf -> G ⊢C bisim_family t cb ->
  G ⊢C family_edge t cf cb p q -> G ⊢C dchild t a p ->
  G ⊢C ∃ (dchild t`[↑] $0 q`[↑] ∧ family_edge t`[↑] cf`[↑] cb`[↑] a`[↑] $0).
Proof.
  intros HF HB Hpq Ha. unfold family_edge in Hpq. fex Hpq r HR. fdestr HR HM Hedge.
  pose proof (family_member_bisim _ t cf cb r HF HB HM) as Hbis.
  pose proof (dbisim_forth _ t r p q a Hbis Hedge Ha) as F.
  fex F b HBb. fdestr HBb Hb Hab. fexists b. fsplit; [exact Hb|].
  unfold family_edge. fexists r. fsplit; assumption.
Qed.

Lemma family_edge_back G t cf cb p q b :
  G ⊢C bisim_family t cf -> G ⊢C bisim_family t cb ->
  G ⊢C family_edge t cf cb p q -> G ⊢C dchild t b q ->
  G ⊢C ∃ (dchild t`[↑] $0 p`[↑] ∧ family_edge t`[↑] cf`[↑] cb`[↑] $0 b`[↑]).
Proof.
  intros HF HB Hpq Hb. unfold family_edge in Hpq. fex Hpq r HR. fdestr HR HM Hedge.
  pose proof (family_member_bisim _ t cf cb r HF HB HM) as Hbis.
  pose proof (dbisim_back _ t r p q b Hbis Hedge Hb) as B.
  fex B a HAa. fdestr HAa Ha Hab. fexists a. fsplit; [exact Ha|].
  unfold family_edge. fexists r. fsplit; assumption.
Qed.

Lemma four_object_container G (HB : incl KBase G) x y cf cb :
  G ⊢C ∃ (raw_transitive $0 ∧
    ((x`[↑] ∈' $0 ∧ y`[↑] ∈' $0) ∧ (cf`[↑] ∈' $0 ∧ cb`[↑] ∈' $0))).
Proof.
  fobtain (KBase_pair _ HB x y) as p1 HP1.
  fobtain (KBase_pair _ HB cf cb) as p2 HP2.
  fobtain (KBase_pair _ HB p1 p2) as p HP.
  fobtain (KBase_transitive _ HB p) as v HV. fdestr HV HpV Htrans.
  unfold raw_pair in HP, HP1, HP2.
  pose proof (raw_transitive_element _ v p p1 Htrans HpV (CE1 (CE1 HP))) as Hp1V.
  pose proof (raw_transitive_element _ v p p2 Htrans HpV (CE2 (CE1 HP))) as Hp2V.
  fexists v. fsplit; [exact Htrans|]. fsplit; fsplit.
  - exact (raw_transitive_element _ v p1 x Htrans Hp1V (CE1 (CE1 HP1))).
  - exact (raw_transitive_element _ v p1 y Htrans Hp1V (CE2 (CE1 HP1))).
  - exact (raw_transitive_element _ v p2 cf Htrans Hp2V (CE1 (CE1 HP2))).
  - exact (raw_transitive_element _ v p2 cb Htrans Hp2V (CE2 (CE1 HP2))).
Qed.

(** Endpoint variables 0/1, then t,x,y,cf,cb as parameters. *)
Definition rooted_union : form :=
  ($0 ≡' $3 ∧ $1 ≡' $4) ∨ family_edge $2 $5 $6 $0 $1.
Lemma rooted_union_bounded : fb 7 rooted_union.
Proof. unfold rooted_union, family_edge, family_member, App0, OP0, Sing0, Pair0. cbn. lia. Qed.

Lemma bisim_union_with_root G (HB : incl KBase G) t x y cf cb :
  In (forall_times 9 (kp0 (tagged_matrix (relation_selector rooted_union)))) G ->
  G ⊢C raw_empty t -> G ⊢C t ∈' x -> G ⊢C t ∈' y ->
  G ⊢C forth_cover t x y cf -> G ⊢C back_cover t x y cb ->
  G ⊢C bisim_family t cf -> G ⊢C bisim_family t cb -> G ⊢C deqv t x y.
Proof.
  intros Hinst Hempty Htx Hty Hforth Hback HF HBk. pose proof (KBase_eq _ HB) as HE.
  fobtain (four_object_container _ HB x y cf cb) as v HV.
  fdestr HV Htrans Hbound. fdestr Hbound HxyV HCC.
  fdestr HxyV HxV HyV. fdestr HCC HcfV HcbV.
  pose proof (KBase_bounded_relation _ HB 5 rooted_union (t .: x .: y .: cf .: cb .: var) t v
    rooted_union_bounded Hinst Hempty) as T.
  fex T s HS. unfold relation_profile in HS. fdestr HS Hts Hedges.
  unfold rooted_union in Hedges. simp_in Hedges.
  fassert Hinclude : (∀ ∀ (family_edge t`[↑]`[↑] cf`[↑]`[↑] cb`[↑]`[↑] $1 $0 →
    App0 s`[↑]`[↑] $1 $0)).
  { fall p. fall q. fintro Hpq.
    pose proof (family_edge_bounds _ t cf cb v p q Htrans HcfV HcbV Hpq) as HPQ.
    pose proof Hedges as H. finst H p q. apply (iff_r _ _ _ H).
    fsplit; [exact HPQ|]. fright. exact Hpq. }
  unfold deqv. fexists s. fsplit.
  - unfold dbisim. fsplit; [exact Hts|]. fall p. fall q. fintro Hpq.
    pose proof Hedges as H. finst H p q.
    pose proof (CE2 (iff_l _ _ _ H Hpq)) as Hcases.
    fcases Hcases Hroot Hfamily.
    + fdestr Hroot Epx Eqy. fsplit; [fsplit; fmemE|]. fsplit.
      * fall a. fintro Ha. unfold dchild in Ha. fdestr Ha Hta Hap.
        fassert Hax : (dchild t a x). { unfold dchild. fsplit; [exact Hta|fmemE]. }
        pose proof Hforth as F. unfold forth_cover in F. finst F a. fmp F Hax.
        fex F r HR. fdestr HR Hrf Hrb. fex Hrb b HBb. fdestr HBb Hb Hab.
        fexists b. fsplit.
        -- unfold dchild in Hb |- *. fsplit; [exact (CE1 Hb)|]. pose proof (CE2 Hb) as Hby. fmemE.
        -- pose proof Hinclude as Hinc. finst Hinc a b. apply (IE Hinc).
           unfold family_edge. fexists r. fsplit; [|exact Hab].
           unfold family_member, dchild in *. fsplit; [exact (CE1 Hrf)|].
           fleft. exact (CE2 Hrf).
      * fall b. fintro Hb. unfold dchild in Hb. fdestr Hb Htb Hbq.
        fassert Hby : (dchild t b y). { unfold dchild. fsplit; [exact Htb|fmemE]. }
        pose proof Hback as B. unfold back_cover in B. finst B b. fmp B Hby.
        fex B r HR. fdestr HR Hrc Hra. fex Hra a HAa. fdestr HAa Ha Hab.
        fexists a. fsplit.
        -- unfold dchild in Ha |- *. fsplit; [exact (CE1 Ha)|]. pose proof (CE2 Ha) as Hax. fmemE.
        -- pose proof Hinclude as Hinc. finst Hinc a b. apply (IE Hinc).
           unfold family_edge. fexists r. fsplit; [|exact Hab].
           unfold family_member, dchild in *. fsplit; [exact (CE1 Hrc)|].
           fright. exact (CE2 Hrc).
    + fsplit; [exact (family_edge_types _ t cf cb p q HF HBk Hfamily)|]. fsplit.
      * fall a. fintro Ha.
        pose proof (family_edge_forth _ t cf cb p q a HF HBk Hfamily Ha) as F.
        fex F b HBb. fdestr HBb Hb Hab. fexists b. fsplit; [exact Hb|].
        pose proof Hinclude as Hinc. finst Hinc a b. exact (IE Hinc Hab).
      * fall b. fintro Hb.
        pose proof (family_edge_back _ t cf cb p q b HF HBk Hfamily Hb) as B.
        fex B a HAa. fdestr HAa Ha Hab. fexists a. fsplit; [exact Ha|].
        pose proof Hinclude as Hinc. finst Hinc a b. exact (IE Hinc Hab).
  - pose proof Hedges as H. finst H x y. apply (iff_r _ _ _ H).
    fsplit; [fsplit; assumption|]. fleft. fsplit; feqE.
Qed.
