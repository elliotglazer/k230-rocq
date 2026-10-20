(** Exact raw constructions from KP0, without Extensionality or Foundation. *)
From Coq Require Import Arith Lia List.
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_F Std_breq.
From OldK230S Require Import KP0 KP0Use.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Definition raw_subset (a b : term) : form :=
  ∀ ($0 ∈' a`[↑] → $0 ∈' b`[↑]).

Lemma raw_subset_subst a b sg :
  (raw_subset a b)[sg] = raw_subset a`[sg] b`[sg].
Proof. psubst raw_subset. Qed.
#[global] Hint Rewrite raw_subset_subst : fsub.
#[global] Arguments raw_subset : simpl never.

Lemma raw_subset_refl G a : G ⊢C raw_subset a a.
Proof. unfold raw_subset. fall z. fintro H. exact H. Qed.

Definition power_matrix : form := $0 ≡' $1 ∧ raw_subset $1 $2.

Lemma power_matrix_bounded : fb 3 power_matrix.
Proof. unfold power_matrix, raw_subset. cbn. lia. Qed.

Lemma kp0_power G (HE : incl EqAx G) a :
  In (forall_times 1 (kp0 power_matrix)) G ->
  G ⊢C ∃ ∀ ($0 ∈' $1 ↔ raw_subset $0 a`[↑]`[↑]).
Proof.
  intros Hin.
  pose proof (kp0_use G 1 power_matrix (a .: var) a Hin power_matrix_bounded) as T.
  fex T C HC. fdestr HC Hrequest Hsupport.
  unfold power_matrix in Hrequest, Hsupport.
  simp_in Hrequest. simp_in Hsupport.
  fassert HaC : (a ∈' C).
  { pose proof Hrequest as H. finst H a.
    fassert Helig : (a ≡' a ∨ ∃ ($0 ∈' C`[↑] ∧ raw_subset a`[↑] $0)).
    { fleft. feqE. }
    fmp H Helig.
    fassert Hwit : (∃ ($0 ≡' a`[↑] ∧ raw_subset a`[↑] a`[↑])).
    { fexists a. fsplit; [feqE | apply raw_subset_refl]. }
    fmp H Hwit. fex H y Hy. fdestr Hy HyC Hyrest. fdestr Hyrest Hya HySub.
    fmemE. }
  fexists C. fall p. fsplit.
  - fintro HpC. pose proof Hsupport as H. finst H p. fmp H HpC.
    fex H u Hu. fdestr Hu Hpu HuSub.
    unfold raw_subset in *. fall z. fintro Hzp. finst HuSub z.
    apply (IE HuSub). fmemE.
  - fintro HpSub. pose proof Hrequest as H. finst H p.
    fassert Helig : (p ≡' a ∨ ∃ ($0 ∈' C`[↑] ∧ raw_subset p`[↑] $0)).
    { fright. fexists a. fsplit; [exact HaC | exact HpSub]. }
    fmp H Helig.
    fassert Hwit : (∃ ($0 ≡' p`[↑] ∧ raw_subset p`[↑] a`[↑])).
    { fexists p. fsplit; [feqE | exact HpSub]. }
    fmp H Hwit. fex H y Hy. fdestr Hy HyC Hyrest. fdestr Hyrest Hyp HySub.
    fmemE.
Qed.

Definition raw_power_axiom : form := ∀ ∃ ∀ ($0 ∈' $1 ↔ raw_subset $0 $2).

Theorem K0_proves_power : K0 ⊢TC raw_power_axiom.
Proof.
  exists (EqAx ++ [forall_times 1 (kp0 power_matrix)]). split.
  - intros b Hb. apply in_app_or in Hb as [Hb|[<-|[]]].
    + apply K0_eq. exact Hb.
    + apply K0_instance, kp0_closed. exact power_matrix_bounded.
  - unfold raw_power_axiom. fall a. apply kp0_power.
    + intros b Hb. cbn in *. tauto.
    + cbn. tauto.
Qed.

Definition raw_singleton (a s : term) : form :=
  a ∈' s ∧ ∀ ($0 ∈' s`[↑] → $0 ≡' a`[↑]).

Lemma raw_singleton_subst a s sg :
  (raw_singleton a s)[sg] = raw_singleton a`[sg] s`[sg].
Proof. psubst raw_singleton. Qed.
#[global] Hint Rewrite raw_singleton_subst : fsub.
#[global] Arguments raw_singleton : simpl never.

Definition singleton_matrix : form := $0 ≡' $2.

Lemma singleton_matrix_bounded : fb 3 singleton_matrix.
Proof. cbn. lia. Qed.

Lemma kp0_singleton G (HE : incl EqAx G) a :
  In (forall_times 1 (kp0 singleton_matrix)) G ->
  G ⊢C ∃ raw_singleton a`[↑] $0.
Proof.
  intros Hin.
  pose proof (kp0_use G 1 singleton_matrix (a .: var) a Hin singleton_matrix_bounded) as T.
  fex T C HC. fdestr HC Hrequest Hsupport.
  unfold singleton_matrix in Hrequest, Hsupport. simp_in Hrequest. simp_in Hsupport.
  fexists C. unfold raw_singleton. fsplit.
  - finst Hrequest a.
    fassert Helig : (a ≡' a ∨ ∃ ($0 ∈' C`[↑] ∧ raw_subset a`[↑] $0)).
    { fleft. feqE. }
    unfold raw_subset in Helig. fmp Hrequest Helig.
    fassert Hwit : (∃ ($0 ≡' a`[↑])). { fexists a. feqE. }
    fmp Hrequest Hwit. fex Hrequest y Hy. fdestr Hy HyC Hya. fmemE.
  - fall z. fintro HzC. finst Hsupport z. fmp Hsupport HzC.
    fex Hsupport p Hp. exact Hp.
Qed.

Definition raw_singleton_axiom : form := ∀ ∃ raw_singleton $1 $0.

Theorem K0_proves_singleton : K0 ⊢TC raw_singleton_axiom.
Proof.
  exists (EqAx ++ [forall_times 1 (kp0 singleton_matrix)]). split.
  - intros b Hb. apply in_app_or in Hb as [Hb|[<-|[]]].
    + apply K0_eq. exact Hb.
    + apply K0_instance, kp0_closed. exact singleton_matrix_bounded.
  - unfold raw_singleton_axiom. fall a. apply kp0_singleton.
    + intros b Hb. cbn in *. tauto.
    + cbn. tauto.
Qed.
