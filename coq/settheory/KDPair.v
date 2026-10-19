(** Nonempty interpreted domain and Pairing in D_t. *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_F Std_breq.
From K230S Require Import KP0 KP0Use KPRaw KPPair KBase KMarkers KDomain KTagged KPrimeTheory.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Definition true_formula : form := ⊥ → ⊥.

Definition domain_pair (t a b c : term) : form :=
  t ∈' c ∧ ∀ (t`[↑] ∈' $0 →
    ($0 ∈' c`[↑] ↔ ($0 ≡' a`[↑] ∨ $0 ≡' b`[↑]))).

Lemma domain_pair_exists G (HB : incl KBase G) t a b :
  In (forall_times 3 (kp0 (tagged_matrix true_formula))) G ->
  G ⊢C raw_empty t -> G ⊢C t ∈' a -> G ⊢C t ∈' b ->
  G ⊢C ∃ domain_pair t`[↑] a`[↑] b`[↑] $0.
Proof.
  intros Hinst Hempty Hta Htb. pose proof (KBase_eq _ HB) as HE.
  fobtain (KBase_pair _ HB a b) as B HP.
  fassert Hne : (¬ (B ≡' t)).
  { fintro E. unfold raw_empty in Hempty. finst Hempty a.
    unfold raw_pair in HP. pose proof (CE1 (CE1 HP)) as HaB.
    apply (IE Hempty). fmemE. }
  fassert HnotB : (¬ (t ∈' B)).
  { fintro HtB. pose proof HP as P. unfold raw_pair in P.
    pose proof (CE2 P) as Hmembers. finst Hmembers t. fmp Hmembers HtB.
    unfold raw_empty in Hempty. finst Hempty t. apply (IE Hempty).
    fcases Hmembers Hta' Htb'; fmemE. }
  pose proof (raw_tagged_comprehension _ HB 0 true_formula var B t
    ltac:(cbn; tauto) Hinst Hempty Hne) as T.
  fex T C HC. unfold true_formula in HC. simp_in HC.
  fexists C. unfold domain_pair. fsplit.
  - pose proof HC as H. finst H t. apply (iff_r _ _ _ H). fright. fleft. feqE.
  - fall x. fintro Htx. fsplit.
    + fintro HxC. pose proof HC as H. finst H x.
      pose proof (iff_l _ _ _ H HxC) as Hcases. fcases Hcases HxB Hrest.
      * fabsurd. apply (IE HnotB). fmemE.
      * fcases Hrest Hxt Hselected.
        -- unfold raw_empty in Hempty. finst Hempty t. fabsurd. apply (IE Hempty). fmemE.
        -- pose proof (CE1 Hselected) as HxB.
           pose proof HP as P. unfold raw_pair in P.
           pose proof (CE2 P) as Hmembers. finst Hmembers x. exact (IE Hmembers HxB).
    + fintro Hcases. pose proof HC as H. finst H x. apply (iff_r _ _ _ H).
      fright. fright. fsplit.
      * unfold raw_pair in HP. fcases Hcases Hxa Hxb.
        -- pose proof (CE1 (CE1 HP)) as HaB. fmemE.
        -- pose proof (CE2 (CE1 HP)) as HbB. fmemE.
      * fintro Hfalse. exact Hfalse.
Qed.

Definition domain_pair_statement : form :=
  ∀ ∀ ∀ (raw_empty $2 → $2 ∈' $1 → $2 ∈' $0 →
    ∃ domain_pair $3 $2 $1 $0).

Theorem K0_proves_domain_pair : K0 ⊢TC domain_pair_statement.
Proof.
  set (inst := forall_times 3 (kp0 (tagged_matrix true_formula))).
  set (B0 := KBase ++ [inst]).
  assert (HB : incl KBase B0) by (intros f Hf; apply in_or_app; now left).
  assert (HI : In inst B0) by (apply in_or_app; right; now left).
  exists B0. split.
  - intros f Hf. apply in_app_or in Hf as [Hf|[<-|[]]].
    + apply KBase_ok, Hf.
    + apply K0_instance, kp0_closed, (tagged_matrix_bounded 0). cbn. tauto.
  - unfold domain_pair_statement. fall t. fall a. fall b.
    match goal with |- ?G ⊢C _ =>
      assert (HB' : incl KBase G) by exact HB;
      assert (HI' : In inst G) by exact HI
    end.
    fintro Hempty. fintro Hta. fintro Htb.
    apply (domain_pair_exists _ HB' t a b HI' Hempty Hta Htb).
Qed.

Theorem K0_domain_inhabited : K0 ⊢TC ∃ (raw_empty $0 ∧ ∃ domain_empty $1 $0).
Proof.
  exists KBase. split; [exact KBase_ok|].
  cbn.
  match goal with |- ?G ⊢C _ =>
    assert (HB : incl KBase G) by (intros a Ha; exact Ha)
  end.
  fobtain (KBase_empty _ HB) as t Ht.
  fexists t. fsplit; [exact Ht|]. apply (domain_empty_exists _ HB t Ht).
Qed.

Corollary KPrimeOrd_proves_domain_pair : KPrimeOrd ⊢TC domain_pair_statement.
Proof. apply K0_derivation_to_KPrimeOrd, K0_proves_domain_pair. Qed.
