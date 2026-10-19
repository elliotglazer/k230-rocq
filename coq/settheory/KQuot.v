(** Bisimulation equality on the tagged domain D_t(x) := t in x. *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_F Std_breq.
From ZFC Require Import Z_base.
From M254S Require Import S_raw.
From K230S Require Import KP0 KP0Use KPRaw KPTransitive KBase KMarkers KTagged KRelation KPrimeTheory.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Definition dchild (t x y : term) : form := t ∈' x ∧ x ∈' y.
#[global] Arguments dchild : simpl never.
Lemma dchild_subst t x y sg : (dchild t x y)[sg] = dchild t`[sg] x`[sg] y`[sg].
Proof. psubst dchild. Qed.
#[global] Hint Rewrite dchild_subst : fsub.

Definition dbisim (t r : term) : form :=
  t ∈' r ∧ ∀ ∀ (App0 r`[↑]`[↑] $1 $0 →
    (t`[↑]`[↑] ∈' $1 ∧ t`[↑]`[↑] ∈' $0) ∧
    ((∀ (dchild t`[↑]`[↑]`[↑] $0 $2 →
         ∃ (dchild t`[↑]`[↑]`[↑]`[↑] $0 $2 ∧ App0 r`[↑]`[↑]`[↑]`[↑] $1 $0))) ∧
     (∀ (dchild t`[↑]`[↑]`[↑] $0 $1 →
         ∃ (dchild t`[↑]`[↑]`[↑]`[↑] $0 $3 ∧ App0 r`[↑]`[↑]`[↑]`[↑] $0 $1))))).

Definition deqv (t x y : term) : form :=
  ∃ (dbisim t`[↑] $0 ∧ App0 $0 x`[↑] y`[↑]).

Definition dmem (t x y : term) : form :=
  ∃ (dchild t`[↑] $0 y`[↑] ∧ deqv t`[↑] x`[↑] $0).

#[global] Arguments dbisim : simpl never.
#[global] Arguments deqv : simpl never.
#[global] Arguments dmem : simpl never.
Lemma dbisim_subst t r sg : (dbisim t r)[sg] = dbisim t`[sg] r`[sg].
Proof. psubst dbisim. Qed.
#[global] Hint Rewrite dbisim_subst : fsub.
Lemma deqv_subst t x y sg : (deqv t x y)[sg] = deqv t`[sg] x`[sg] y`[sg].
Proof. psubst deqv. Qed.
#[global] Hint Rewrite deqv_subst : fsub.
Lemma dmem_subst t x y sg : (dmem t x y)[sg] = dmem t`[sg] x`[sg] y`[sg].
Proof. psubst dmem. Qed.
#[global] Hint Rewrite dmem_subst : fsub.

Lemma raw_transitive_element G v x y :
  G ⊢C raw_transitive v -> G ⊢C x ∈' v -> G ⊢C y ∈' x -> G ⊢C y ∈' v.
Proof.
  intros H Hx Hy. unfold raw_transitive in H. finst H x. fmp H Hx.
  unfold raw_subset in H. finst H y. exact (IE H Hy).
Qed.

Definition domain_diagonal : form := $0 ≡' $1 ∧ $2 ∈' $0.
Lemma domain_diagonal_bounded : fb 3 domain_diagonal.
Proof. cbn. lia. Qed.

Lemma deqv_refl G (HB : incl KBase G) t x :
  In (forall_times 5 (kp0 (tagged_matrix (relation_selector domain_diagonal)))) G ->
  G ⊢C raw_empty t -> G ⊢C t ∈' x -> G ⊢C deqv t x x.
Proof.
  intros Hinst Hempty Htx. pose proof (KBase_eq _ HB) as HE.
  fobtain (KBase_transitive _ HB x) as v HV. fdestr HV HxV Htrans.
  pose proof (KBase_bounded_relation _ HB 1 domain_diagonal (t .: var) t v
    domain_diagonal_bounded Hinst Hempty) as T.
  fex T r HR. unfold relation_profile in HR. fdestr HR Htr Hedges.
  unfold domain_diagonal in Hedges. simp_in Hedges.
  fassert Hdiag : (∀ (dchild t`[↑] $0 v`[↑] → App0 r`[↑] $0 $0)).
  { fall a. fintro Ha. unfold dchild in Ha. fdestr Ha Hta HaV.
    pose proof Hedges as H. finst H a a. apply (iff_r _ _ _ H).
    fsplit; [fsplit; exact HaV|]. fsplit; [feqE|exact Hta]. }
  unfold deqv. fexists r. fsplit.
  - unfold dbisim. fsplit; [exact Htr|]. fall p. fall q. fintro Hpq.
    pose proof Hedges as H. finst H p q.
    pose proof (iff_l _ _ _ H Hpq) as HF. fdestr HF HVpq HEpq.
    fdestr HVpq HpV HqV. fdestr HEpq Epq Htp.
    fsplit; [fsplit; [exact Htp|fmemE]|]. fsplit.
    + fall a. fintro Ha. unfold dchild in Ha. fdestr Ha Hta Hap.
      fexists a. fsplit.
      * unfold dchild. fsplit; [exact Hta|fmemE].
      * pose proof Hdiag as Hstep. finst Hstep a. apply (IE Hstep).
        unfold dchild. fsplit; [exact Hta|].
        exact (raw_transitive_element _ v p a Htrans HpV Hap).
    + fall b. fintro Hb. unfold dchild in Hb. fdestr Hb Htb Hbq.
      fexists b. fsplit.
      * unfold dchild. fsplit; [exact Htb|fmemE].
      * pose proof Hdiag as Hstep. finst Hstep b. apply (IE Hstep).
        unfold dchild. fsplit; [exact Htb|].
        exact (raw_transitive_element _ v q b Htrans HqV Hbq).
  - finst Hdiag x. apply (IE Hdiag). unfold dchild. fsplit; assumption.
Qed.

Definition deqv_refl_statement : form :=
  ∀ ∀ (raw_empty $1 → $1 ∈' $0 → deqv $1 $0 $0).

Theorem K0_proves_deqv_refl : K0 ⊢TC deqv_refl_statement.
Proof.
  set (ri := forall_times 5 (kp0 (tagged_matrix (relation_selector domain_diagonal)))).
  set (B0 := KBase ++ [ri]).
  assert (HB : incl KBase B0) by (intros b Hb; apply in_or_app; now left).
  assert (HRI : In ri B0) by (apply in_or_app; right; now left).
  exists B0. split.
  - intros b Hb. apply in_app_or in Hb as [Hb|[<-|[]]].
    + apply KBase_ok, Hb.
    + apply K0_instance, kp0_closed, tagged_matrix_bounded, relation_selector_bounded.
      exact domain_diagonal_bounded.
  - unfold deqv_refl_statement. fall t. fall x.
    match goal with |- ?G ⊢C _ =>
      assert (HB' : incl KBase G) by exact HB;
      assert (HRI' : In ri G) by exact HRI
    end.
    fintro Hempty. fintro Htx. exact (deqv_refl _ HB' t x HRI' Hempty Htx).
Qed.

Corollary KPrimeOrd_proves_deqv_refl : KPrimeOrd ⊢TC deqv_refl_statement.
Proof. apply K0_derivation_to_KPrimeOrd, K0_proves_deqv_refl. Qed.
