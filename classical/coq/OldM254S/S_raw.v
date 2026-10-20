(** * S_raw: raw set theory in S0 (no extensionality)

    Endpoint uniqueness of Kuratowski codes from the equality axioms alone ([op_inj]). *)
From Coq Require Import Arith Lia List.
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_F Std_breq.
From OldZFC Require Import Z_rel Z_base.
From OldM254S Require Import S_def S_gic.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.
#[local] Set Default Proof Using "All".

Section Eq.
Context {G : list form} (HE : incl EqAx G).

Lemma sing0_el x s z : G ⊢C Sing0 x s -> G ⊢C z ∈' s -> G ⊢C z ≡' x.
Proof. intros H Hz. unfold Sing0 in H. fdestr H H1 H2. finst H2 z. exact (IE H2 Hz). Qed.

Lemma sing0_in x s : G ⊢C Sing0 x s -> G ⊢C x ∈' s.
Proof. intros H. unfold Sing0 in H. exact (CE1 H). Qed.

Lemma pair0_el x y p z : G ⊢C Pair0 x y p -> G ⊢C z ∈' p -> G ⊢C z ≡' x ∨ z ≡' y.
Proof. intros H Hz. unfold Pair0 in H. fdestr H H1 H2. finst H2 z. exact (IE H2 Hz). Qed.

Lemma pair0_inl x y p : G ⊢C Pair0 x y p -> G ⊢C x ∈' p.
Proof. intros H. unfold Pair0 in H. exact (CE1 (CE1 H)). Qed.

Lemma pair0_inr x y p : G ⊢C Pair0 x y p -> G ⊢C y ∈' p.
Proof. intros H. unfold Pair0 in H. exact (CE2 (CE1 H)). Qed.

Lemma op0_kinds x y c e : G ⊢C OP0 x y c -> G ⊢C e ∈' c -> G ⊢C Sing0 x e ∨ Pair0 x y e.
Proof. intros H He. unfold OP0 in H. fdestr H H12 H3. finst H3 e. exact (IE H3 He). Qed.

End Eq.

Lemma op_inj {G} (HE : incl EqAx G) x y x' y' c :
  G ⊢C OP0 x y c -> G ⊢C OP0 x' y' c -> G ⊢C x ≡' x' ∧ y ≡' y'.
Proof.
  intros H H'.
  assert (Hx : G ⊢C x ≡' x').
  { pose proof H' as T. unfold OP0 in T. fdestr T T12 T3. fdestr T12 T1 T2. fex T1 s' Hs'. fdestr Hs' Hs'c Hs'1.
    fhave K : (op0_kinds HE x y c s' H Hs'c). fcases K K1 K2.
    - fhave E : (sing0_el HE x s' x' K1 (sing0_in HE x' s' Hs'1)). feqE.
    - fhave E : (sing0_el HE x' s' x Hs'1 (pair0_inl HE x y s' K2)). feqE. }
  fsplit; [exact Hx|].
  pose proof H' as T. unfold OP0 in T. fdestr T T12 T3. fdestr T12 T1 T2. fex T2 t' Ht'. fdestr Ht' Ht'c Ht'1.
  fhave Hy't' : (pair0_inr HE x' y' t' Ht'1).
  fhave K : (op0_kinds HE x y c t' H Ht'c). fcases K K1 K2.
  - fhave E1 : (sing0_el HE x t' y' K1 Hy't').
    pose proof H as U. unfold OP0 in U. fdestr U U12 U3. fdestr U12 U1 U2. fex U2 t Ht. fdestr Ht Htc Ht1.
    fhave Hyt : (pair0_inr HE x y t Ht1).
    fhave K' : (op0_kinds HE x' y' c t H' Htc). fcases K' K3 K4.
    + fhave E2 : (sing0_el HE x' t y K3 Hyt). feqE_at 4.
    + fhave E2 : (pair0_el HE x' y' t y K4 Hyt). fcases E2 E3 E4; feqE_at 4.
  - fhave E1 : (pair0_el HE x y t' y' K2 Hy't'). fcases E1 E3 E4.
    + fhave E5 : (pair0_el HE x' y' t' y Ht'1 (pair0_inr HE x y t' K2)). fcases E5 E6 E7; feqE_at 4.
    + feqE.
Qed.

(** ** Fixed GIC closures used here *)
Definition th_pair : form := ($0 ≡' $2 ∧ $1 ≡' $4) ∨ ($0 ≡' $3 ∧ $1 ≡' $5).
Definition psi_union : form := ∃ ($0 ∈' $2 ∧ $1 ∈' $0).

Definition Sq_raw : list form :=
  [forall_times 1 (gic (sep_th ⊥)); forall_times 4 (gic th_pair); forall_times 2 (gic (sep_th psi_union))].

Lemma Sq_raw_ok a : In a Sq_raw -> S0 a.
Proof.
  intros [<-|[<-|[<-|[]]]]; apply S0_gic, gic_closed.
  - apply (fb_sep_th 0). exact I.
  - cbn. lia.
  - apply (fb_sep_th 1). cbn. lia.
Qed.

(** ** The container axiom *)
Definition CPV (V : term) : form :=
  ∀ ($0 ∈' V`[↑] → Sub0 $0 V`[↑] ∧ ∃ ($0 ∈' V`[↑]`[↑] ∧ ∀ (Sub0 $0 $2 → $0 ∈' $1))).
#[global] Arguments CPV : simpl never.
Lemma CPV_subst V sg : (CPV V)[sg] = CPV V`[sg].
Proof. psubst CPV. Qed.
#[global] Hint Rewrite CPV_subst : fsub.

Lemma HE_of {G} (HB : incl Sbase G) : incl EqAx G.
Proof. intros a Ha. apply HB. cbn in *. tauto. Qed.

Lemma cp_ex {G} (HB : incl Sbase G) p : G ⊢C ∃ (p`[↑] ∈' $0 ∧ CPV $0).
Proof.
  assert (H : G ⊢C ax_cp) by (apply Ctx, HB; cbn; tauto). finst H p.
  unfold CPV, Sub0. cbn. cbn in H. exact H.
Qed.

Lemma cp_trans {G} V x z : G ⊢C CPV V -> G ⊢C x ∈' V -> G ⊢C z ∈' x -> G ⊢C z ∈' V.
Proof.
  intros H Hx Hz. unfold CPV in H. finst H x. fmp H Hx. fdestr H H1 H2. unfold Sub0 in H1.
  finst H1 z. exact (IE H1 Hz).
Qed.

Lemma cp_pow {G} V x : G ⊢C CPV V -> G ⊢C x ∈' V ->
  G ⊢C ∃ ($0 ∈' V`[↑] ∧ ∀ (Sub0 $0 x`[↑]`[↑] → $0 ∈' $1)).
Proof. intros H Hx. unfold CPV in H. finst H x. fmp H Hx. exact (CE2 H). Qed.

Lemma emp_ex {G} (HB : incl Sbase G) (HR : incl Sq_raw G) : G ⊢C ∃ Emp0 $0.
Proof.
  assert (Hin : In (forall_times 1 (gic (sep_th ⊥))) G) by (apply HR; cbn; tauto).
  pose proof (sepS_use G 0 ⊥ var $0 (HE_of HB) Hin I) as T. fex T C HC. fexists C.
  unfold Emp0. fall z. fintro Hz. finst HC z. fhave T : (iff_l _ _ _ HC Hz). exact (CE2 T).
Qed.

Lemma emp_not {G} e z : G ⊢C Emp0 e -> G ⊢C z ∈' e -> G ⊢C ⊥.
Proof. intros H Hz. unfold Emp0 in H. finst H z. exact (IE H Hz). Qed.

Lemma pair_ex {G} (HB : incl Sbase G) (HR : incl Sq_raw G) a b : G ⊢C ∃ Pair0 a`[↑] b`[↑] $0.
Proof.
  pose proof (HE_of HB) as HE.
  fobtain (emp_ex HB HR) as e He.
  fobtain (cp_ex HB e) as V HV0. fdestr HV0 HeV HV.
  fobtain (cp_pow V e HV HeV) as W HW0. fdestr HW0 HWV HW.
  fassert HeW : (e ∈' W).
  { finst HW e. apply (IE HW). unfold Sub0. fall z. fintro Hz. exact Hz. }
  fassert Hne : (e ≡' W → ⊥).
  { fintro E. apply (emp_not e e He). fmemE. }
  pose proof (HR (forall_times 4 (gic th_pair)) ltac:(cbn; tauto)) as Hin.
  pose proof (gic_use _ 4 th_pair (e .: W .: a .: b .: var) V Hin ltac:(cbn; lia)) as T.
  fex T C HC. fdestr HC Hcov Hnx. fexists C. unfold Pair0, th_pair in *. simp_in Hcov. simp_in Hnx.
  fsplit; [fsplit|].
  - pose proof Hcov as H. finst H e. fmp H HeV. finst H a.
    fassert A : ((e ≡' e ∧ a ≡' a) ∨ (e ≡' W ∧ a ≡' b)).
    { fleft. fsplit; feqE. }
    fmp H A. fex H y Hy. fdestr Hy Hy1 Hy2. fcases Hy1 Hy3 Hy4.
    + fdestr Hy3 Hy5 Hy6. fmemE.
    + fdestr Hy4 Hy5 Hy6. fabsurd. exact (IE Hne Hy5).
  - pose proof Hcov as H. finst H W. fmp H HWV. finst H b.
    fassert A : ((W ≡' e ∧ b ≡' a) ∨ (W ≡' W ∧ b ≡' b)).
    { fright. fsplit; feqE. }
    fmp H A. fex H y Hy. fdestr Hy Hy1 Hy2. fcases Hy1 Hy3 Hy4.
    + fdestr Hy3 Hy5 Hy6. fabsurd. apply (IE Hne). feqE.
    + fdestr Hy4 Hy5 Hy6. fmemE.
  - fall z. fintro Hz. finst Hnx z. fmp Hnx Hz. fex Hnx u Hu. fcases Hu H1 H2.
    + fleft. exact (CE2 H1).
    + fright. exact (CE2 H2).
Qed.


Lemma union_ex {G} (HB : incl Sbase G) (HR : incl Sq_raw G) x : G ⊢C ∃ Union0 x`[↑] $0.
Proof.
  pose proof (HE_of HB) as HE.
  fobtain (cp_ex HB x) as V HV0. fdestr HV0 HxV HV.
  pose proof (HR (forall_times 2 (gic (sep_th psi_union))) ltac:(cbn; tauto)) as Hin.
  pose proof (sepS_use _ 1 psi_union (x .: var) V HE Hin ltac:(cbn; lia)) as T.
  fex T U HU. fexists U. unfold psi_union in HU. simp_in HU. unfold Union0. fsplit.
  - fall z. fintro Hz. finst HU z. fhave T : (iff_l _ _ _ HU Hz). exact (CE2 T).
  - fall t. fintro Ht. fall z. fintro Hz. finst HU z. apply (iff_r _ _ _ HU). fsplit.
    + exact (cp_trans V t z HV (cp_trans V x t HV HxV Ht) Hz).
    + fexists t. fsplit; [exact Ht | exact Hz].
Qed.

Lemma sing_of_pair {G} (HE : incl EqAx G) x s : G ⊢C Pair0 x x s -> G ⊢C Sing0 x s.
Proof.
  intros H. unfold Sing0. fsplit; [exact (pair0_inl HE x x s H)|].
  fall z. fintro Hz. fhave E : (pair0_el HE x x s z H Hz). fcases E E1 E2; exact E1 || exact E2.
Qed.

Lemma op_ex {G} (HB : incl Sbase G) (HR : incl Sq_raw G) x y : G ⊢C ∃ OP0 x`[↑] y`[↑] $0.
Proof.
  pose proof (HE_of HB) as HE.
  fobtain (pair_ex HB HR x x) as s Hs. fhave Hs' : (sing_of_pair HE x s Hs).
  fobtain (pair_ex HB HR x y) as t Ht. fobtain (pair_ex HB HR s t) as c Hc.
  fexists c. unfold OP0. fsplit; [fsplit|].
  - fexists s. fsplit; [exact (pair0_inl HE s t c Hc) | exact Hs'].
  - fexists t. fsplit; [exact (pair0_inr HE s t c Hc) | exact Ht].
  - fall e. fintro He. fhave E : (pair0_el HE s t c e Hc He). fcases E E1 E2.
    + fleft. frewE E1 (Sing0 x`[↑] $0). exact Hs'.
    + fright. frewE E2 (Pair0 x`[↑] y`[↑] $0). exact Ht.
Qed.

Lemma codes_ex {G} (HB : incl Sbase G) W :
  G ⊢C ∃ ∀ ($0 ∈' W`[↑]`[↑] → ∀ ($0 ∈' W`[↑]`[↑]`[↑] → ∀ (OP0 $2 $1 $0 → $0 ∈' $3))).
Proof.
  pose proof (HE_of HB) as HE.
  fobtain (cp_ex HB W) as V HV0. fdestr HV0 HWV HV.
  fobtain (cp_pow V W HV HWV) as Q HQ0. fdestr HQ0 HQV HQ.
  fobtain (cp_pow V Q HV HQV) as D HD0. fdestr HD0 HDV HD.
  fexists D. fall x. fintro Hx. fall y. fintro Hy. fall c. fintro Hc.
  finst HD c. apply (IE HD). unfold Sub0. fall e. fintro He. finst HQ e. apply (IE HQ).
  unfold Sub0. fall z. fintro Hz.
  fhave K : (op0_kinds HE x y c e Hc He). fcases K K1 K2.
  - fhave E : (sing0_el HE x e z K1 Hz). fmemE.
  - fhave E : (pair0_el HE x y e z K2 Hz). fcases E E1 E2; fmemE.
Qed.

Lemma app_in {G} V R x y : G ⊢C CPV V -> G ⊢C R ∈' V -> G ⊢C App0 R x y -> G ⊢C x ∈' V ∧ y ∈' V.
Proof.
  intros HV HR Ha. unfold App0 in Ha. fex Ha c Hc. fdestr Hc HcR Hop.
  fhave HcV : (cp_trans V R c HV HR HcR).
  unfold OP0 in Hop. fdestr Hop H12 H3. fdestr H12 H1 H2. fsplit.
  - fex H1 s Hs. fdestr Hs Hsc Hs1. unfold Sing0 in Hs1. fdestr Hs1 Hxs Hs2.
    exact (cp_trans V s x HV (cp_trans V c s HV HcV Hsc) Hxs).
  - fex H2 t Ht. fdestr Ht Htc Ht1. unfold Pair0 in Ht1. fdestr Ht1 Ht2 Ht3. fdestr Ht2 Hxt Hyt.
    exact (cp_trans V t y HV (cp_trans V c t HV HcV Htc) Hyt).
Qed.
