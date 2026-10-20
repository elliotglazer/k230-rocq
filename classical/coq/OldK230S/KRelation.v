(** Exact bounded relations from tagged comprehension. Neither marker can be
    an ordered-pair code, so App0 sees exactly the selected endpoint pairs. *)
From Coq Require Import Arith Lia List.
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_F Std_breq.
From OldZFC Require Import Z_base.
From OldM254S Require Import S_raw.
From OldK230S Require Import KP0 KP0Use KPRaw KBase KMarkers KTagged KOrderedPair KPrimeTheory.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Lemma ordered_pair_not_empty G (HE : incl EqAx G) t x y c :
  G ⊢C raw_empty t -> G ⊢C OP0 x y c -> G ⊢C ¬ (c ≡' t).
Proof.
  intros Hempty Hcode. fintro E.
  unfold OP0 in Hcode. pose proof (CE1 (CE1 Hcode)) as Hex.
  fex Hex s Hs. pose proof (CE1 Hs) as Hsc.
  unfold raw_empty in Hempty. finst Hempty s. apply (IE Hempty). fmemE.
Qed.

(** The selected code is 0, the endpoint bound is 1, then theta's parameters.
    In theta, index 0 is the first endpoint and index 1 the second. *)
Definition relation_selector (theta : form) : form :=
  ∃ ∃ (($1 ∈' $3 ∧ $0 ∈' $3) ∧
    (OP0 $1 $0 $2 ∧ theta[$1 .: $0 .: (fun k => $(4 + k))])).

Lemma relation_selector_bounded n theta : fb (S (S n)) theta ->
  fb (S (S n)) (relation_selector theta).
Proof.
  intros H. unfold relation_selector, OP0, Sing0, Pair0. cbn.
  repeat split; try lia. eapply fb_subst; [exact H|].
  intros [|[|k]] Hk; cbn; lia.
Qed.

Definition relation_profile (t w r : term) (theta : form) (rho : nat -> term) : form :=
  t ∈' r ∧ ∀ ∀ (App0 r`[↑]`[↑] $1 $0 ↔
    (($1 ∈' w`[↑]`[↑] ∧ $0 ∈' w`[↑]`[↑]) ∧
     theta[$1 .: $0 .: (fun k => (rho k)`[↑]`[↑])])).

#[global] Arguments relation_profile : simpl never.
Lemma relation_profile_subst t w r theta rho sg :
  (relation_profile t w r theta rho)[sg] =
  relation_profile t`[sg] w`[sg] r`[sg] theta (fun k => (rho k)`[sg]).
Proof. unfold relation_profile. cbn. autorewrite with fsub. kform_eq. Qed.
#[global] Hint Rewrite relation_profile_subst : fsub.

Lemma KBase_bounded_relation G (HB : incl KBase G) n theta (sg : nat -> term) t w :
  fb (S (S n)) theta ->
  In (forall_times (S (S (S (S n)))) (kp0 (tagged_matrix (relation_selector theta)))) G ->
  G ⊢C raw_empty t ->
  G ⊢C ∃ relation_profile t`[↑] w`[↑] $0 theta (fun k => (sg k)`[↑]).
Proof.
  intros Hfb Hinst Hempty. pose proof (KBase_eq _ HB) as HE.
  fobtain (KBase_code_bound _ HB t w Hempty) as d HD.
  fdestr HD Htd Hbound.
  fassert Hdt : (¬ (d ≡' t)).
  { fintro E. unfold raw_empty in Hempty. finst Hempty t.
    apply (IE Hempty). fmemE. }
  pose proof (raw_tagged_comprehension _ HB (S n) (relation_selector theta) (w .: sg) d t
    (relation_selector_bounded n theta Hfb) Hinst Hempty Hdt) as T.
  fex T r HR. unfold relation_selector in HR. simp_in HR.
  fexists r. unfold relation_profile. fsplit.
  - pose proof HR as H. finst H t. apply (iff_r _ _ _ H). fright. fleft. feqE.
  - fall x. fall y. fsplit.
    + fintro Hxy. unfold App0 in Hxy. fex Hxy c HC. fdestr HC Hcr Hcode.
      pose proof HR as H. finst H c. pose proof (iff_l _ _ _ H Hcr) as Hcases.
      fcases Hcases Hcd Hrest.
      * fassert Htc : (t ∈' c). { fmemE. }
        fabsurd. exact (ordered_pair_no_empty_member _ HE t x y c Hempty Hcode Htc).
      * fcases Hrest Hct Hselected.
        -- fabsurd. exact (IE (ordered_pair_not_empty _ HE t x y c Hempty Hcode) Hct).
        -- pose proof (CE2 Hselected) as Hsel. fex Hsel u Hu. fex Hu v Hv.
           fdestr Hv HuvW Huv. fdestr Huv Huvcode Htheta.
           pose proof (op_inj HE x y u v c Hcode Huvcode) as E.
           fdestr E Efirst Esecond. fsplit.
           ++ fsplit; [pose proof (CE1 HuvW) as HuW|pose proof (CE2 HuvW) as HvW]; fmemE.
           ++ fassert Htheta' : (theta[u .: v .: sg]). { kconv Htheta. }
              fassert Htheta'' : (theta[x .: y .: sg]).
              { eapply (leibE_gen theta _ (u .: v .: sg) (x .: y .: sg) HE); [|exact Htheta'].
                intros [|[|k]]; cbn; feqE. }
              kconv Htheta''.
    + fintro Hselected. fdestr Hselected HxyW Htheta.
      fobtain (KBase_ordered_pair _ HB x y) as c Hcode.
      unfold App0. fexists c. fsplit; [|exact Hcode].
      pose proof HR as H. finst H c. apply (iff_r _ _ _ H). fright. fright. fsplit.
      * unfold codes_over in Hbound. finst Hbound x. fmp Hbound (CE1 HxyW).
        finst Hbound y. fmp Hbound (CE2 HxyW). finst Hbound c. exact (IE Hbound Hcode).
      * fexists x. fexists y. fsplit; [exact HxyW|]. fsplit; [exact Hcode|]. kconv Htheta.
Qed.

Definition bounded_relation_statement (theta : form) : form :=
  ∀ ∀ (raw_empty $0 → ∃ relation_profile $1 $2 $0 theta (fun k => $(3 + k))).

Theorem K0_proves_bounded_relation n theta : fb (S (S n)) theta ->
  K0 ⊢TC forall_times n (bounded_relation_statement theta).
Proof.
  intros Hfb.
  set (ri := forall_times (S (S (S (S n)))) (kp0 (tagged_matrix (relation_selector theta)))).
  set (B0 := KBase ++ [ri]).
  assert (HB : incl KBase B0) by (intros b Hb; apply in_or_app; now left).
  assert (HRI : In ri B0) by (apply in_or_app; right; now left).
  exists B0. split.
  - intros b Hb. apply in_app_or in Hb as [Hb|[<-|[]]].
    + apply KBase_ok, Hb.
    + apply K0_instance, kp0_closed, tagged_matrix_bounded, relation_selector_bounded, Hfb.
  - apply ft_intro. intros sg. unfold bounded_relation_statement. cbn.
    fall w. fall t.
    match goal with |- ?G ⊢C _ =>
      assert (HB' : incl KBase G) by exact HB;
      assert (HRI' : In ri G) by exact HRI
    end.
    fintro Hempty.
    pose proof (KBase_bounded_relation _ HB' n theta sg t w Hfb HRI' Hempty) as T.
    unfold relation_profile in T |- *. cbn. kconv T.
Qed.

Corollary KPrimeOrd_proves_bounded_relation n theta : fb (S (S n)) theta ->
  KPrimeOrd ⊢TC forall_times n (bounded_relation_statement theta).
Proof. intros H. apply K0_derivation_to_KPrimeOrd, K0_proves_bounded_relation, H. Qed.
