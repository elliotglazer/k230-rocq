(** Pairing from three KP0 instances. The markers are constructed and discharged. *)
From Coq Require Import Arith Lia List.
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_F Std_breq.
From OldK230S Require Import KP0 KP0Use KPRaw.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Definition raw_pair (a b c : term) : form :=
  (a ∈' c ∧ b ∈' c) ∧ ∀ ($0 ∈' c`[↑] → ($0 ≡' a`[↑] ∨ $0 ≡' b`[↑])).

Lemma raw_pair_subst a b c sg :
  (raw_pair a b c)[sg] = raw_pair a`[sg] b`[sg] c`[sg].
Proof. psubst raw_pair. Qed.
#[global] Hint Rewrite raw_pair_subst : fsub.
#[global] Arguments raw_pair : simpl never.

(** Parameter order: a, b, empty marker t, singleton marker s. *)
Definition pair_matrix : form :=
  ($1 ≡' $5 ∧ $0 ≡' $2) ∨ ($1 ≡' $4 ∧ $0 ≡' $3).

Lemma pair_matrix_bounded : fb 6 pair_matrix.
Proof. cbn. lia. Qed.

Lemma kp0_pair G (HE : incl EqAx G) a b :
  In (kp0 ⊥) G -> In (forall_times 1 (kp0 singleton_matrix)) G ->
  In (forall_times 4 (kp0 pair_matrix)) G ->
  G ⊢C ∃ raw_pair a`[↑] b`[↑] $0.
Proof.
  intros Hempty Hsingleton Hpair.
  fobtain (kp0_empty G Hempty) as t Ht.
  fobtain (kp0_singleton _ HE t Hsingleton) as s Hs.
  fassert Hts : (t ≡' s → ⊥).
  { fintro E. pose proof (CE1 Hs) as HtS.
    finst Ht t. apply (IE Ht). fmemE. }
  pose proof (kp0_use _ 4 pair_matrix (a .: b .: t .: s .: var) s Hpair pair_matrix_bounded) as T.
  fex T C HC. fdestr HC Hrequest Hsupport.
  unfold pair_matrix in Hrequest, Hsupport. simp_in Hrequest. simp_in Hsupport.
  fassert HaC : (a ∈' C).
  { pose proof Hrequest as H. finst H s.
    fassert Helig : (s ≡' s ∨ ∃ ($0 ∈' C`[↑] ∧ raw_subset s`[↑] $0)).
    { fleft. feqE. }
    unfold raw_subset in Helig. fmp H Helig.
    fassert Hwit : (∃ ((s`[↑] ≡' s`[↑] ∧ $0 ≡' a`[↑]) ∨
                       (s`[↑] ≡' t`[↑] ∧ $0 ≡' b`[↑]))).
    { fexists a. fleft. fsplit; feqE. }
    fmp H Hwit. fex H y Hy. fdestr Hy HyC Hycases.
    fcases Hycases Hleft Hright.
    - fdestr Hleft Hss Hya. fmemE.
    - fdestr Hright Hst Hyb. fabsurd. apply (IE Hts). feqE. }
  fassert HbC : (b ∈' C).
  { pose proof Hrequest as H. finst H t.
    fassert Helig : (t ≡' s ∨ ∃ ($0 ∈' C`[↑] ∧ raw_subset t`[↑] $0)).
    { fright. fexists a. fsplit; [exact HaC|].
      unfold raw_subset. fall z. fintro Hzt. finst Ht z. fabsurd. exact (IE Ht Hzt). }
    unfold raw_subset in Helig. fmp H Helig.
    fassert Hwit : (∃ ((t`[↑] ≡' s`[↑] ∧ $0 ≡' a`[↑]) ∨
                       (t`[↑] ≡' t`[↑] ∧ $0 ≡' b`[↑]))).
    { fexists b. fright. fsplit; feqE. }
    fmp H Hwit. fex H y Hy. fdestr Hy HyC Hycases.
    fcases Hycases Hleft Hright.
    - fdestr Hleft Hts' Hya. fabsurd. exact (IE Hts Hts').
    - fdestr Hright Htt Hyb. fmemE. }
  fexists C. unfold raw_pair. fsplit.
  - fsplit; assumption.
  - fall z. fintro HzC. finst Hsupport z. fmp Hsupport HzC.
    fex Hsupport p Hp. fcases Hp Hleft Hright.
    + fleft. exact (CE2 Hleft).
    + fright. exact (CE2 Hright).
Qed.

Definition raw_pair_axiom : form := ∀ ∀ ∃ raw_pair $2 $1 $0.

Theorem K0_proves_pair : K0 ⊢TC raw_pair_axiom.
Proof.
  exists (EqAx ++ [kp0 ⊥; forall_times 1 (kp0 singleton_matrix);
                  forall_times 4 (kp0 pair_matrix)]). split.
  - intros b Hb. apply in_app_or in Hb as [Hb|[<-|[<-|[<-|[]]]]].
    + apply K0_eq. exact Hb.
    + apply (K0_instance ⊥ 0), kp0_closed. exact I.
    + apply K0_instance, kp0_closed. exact singleton_matrix_bounded.
    + apply K0_instance, kp0_closed. exact pair_matrix_bounded.
  - unfold raw_pair_axiom. fall a. fall b. apply kp0_pair.
    + intros f Hf. cbn in *. tauto.
    + cbn. tauto.
    + cbn. tauto.
    + cbn. tauto.
Qed.
