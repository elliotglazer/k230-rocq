(** One direction of the ordinary/numerical source comparison.  This theory
    consists of equality axioms and closed decodings of the actual gated
    source bundle.  Identifying it with the running proof enumerator, and
    validating all its instances in the reverse direction, remain separate. *)
From Coq Require Import Arith Lia List.
From OldUndecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_tr Std_gen Std_iface Std_iface2 Std_setnd Std_F.
From OldK230S Require Import KPrimeCore KPrimeTheory KCode230 KDecoder230
  KDecodeTranslate KDecodeCore.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Inductive DecodedK230Ord : form -> Prop :=
  | DecodedK230Ord_eq phi : In phi EqAx -> DecodedK230Ord phi
  | DecodedK230Ord_bundle a b c n : maxfr (D (gated230 a b c)) < n ->
      DecodedK230Ord (Lib n (D (gated230 a b c))).

Lemma DecodedK230Ord_closed phi : DecodedK230Ord phi -> closedf phi.
Proof.
  intros [p Hp|a b c n Hn].
  - apply KPrimeOrd_closed. apply KPrimeOrd_eq. exact Hp.
  - apply Lib_closed. exact Hn.
Qed.

Theorem DecodedK230Ord_proves_kprime n phi :
  DecodedK230Ord ⊢TC forall_times n (kprime_core phi).
Proof.
  destruct (fb_exists phi) as [N HN].
  set (B := EqAx ++ [ordinary_source230 phi]).
  assert (HE : incl EqAx B) by (intros p Hp; apply in_or_app; now left).
  assert (HB : forall p, In p B -> DecodedK230Ord p).
  { intros p Hp. apply in_app_or in Hp as [Hp|[<-|[]]].
    - now apply DecodedK230Ord_eq.
    - unfold ordinary_source230. apply DecodedK230Ord_bundle. lia. }
  assert (HC : forall p, In p B -> closedf p).
  { intros p Hp. apply DecodedK230Ord_closed, HB, Hp. }
  exists B. split; [exact HB|].
  apply forall_times_intro_closed; [exact HC|].
  apply (ordinary_source230_to_kprime B phi N HE HN).
  apply Ctx, in_or_app. right. now left.
Qed.

Theorem KPrimeOrd_derivation_to_DecodedK230Ord phi :
  KPrimeOrd ⊢TC phi -> DecodedK230Ord ⊢TC phi.
Proof.
  apply theory_derivation_map. intros p Hp. destruct Hp as [p Hp|p n Hp].
  - exists [p]. split.
    + intros q [<-|[]]. now apply DecodedK230Ord_eq.
    + apply Ctx. now left.
  - apply DecodedK230Ord_proves_kprime.
Qed.
