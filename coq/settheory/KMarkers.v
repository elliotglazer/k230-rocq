(** Marker separation uses only object-level equality and membership. *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_F Std_breq.
From K230S Require Import KP0 KPRaw KPPair KBase.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Definition raw_empty (t : term) : form := ∀ ($0 ∈' t`[↑] → ⊥).
Lemma raw_empty_subst t sg : (raw_empty t)[sg] = raw_empty t`[sg].
Proof. psubst raw_empty. Qed.
#[global] Hint Rewrite raw_empty_subst : fsub.
#[global] Arguments raw_empty : simpl never.

Lemma singleton_container G (HE : incl EqAx G) x p r :
  G ⊢C p ≡' r -> G ⊢C raw_singleton x p -> G ⊢C raw_singleton x r.
Proof.
  intros E H. unfold raw_singleton in *. fsplit.
  - pose proof (CE1 H) as Hxp. fmemE.
  - fall z. fintro Hzr. pose proof (CE2 H) as Hprofile. finst Hprofile z.
    apply (IE Hprofile). fmemE.
Qed.

Lemma empty_not_singleton G t x :
  G ⊢C raw_empty t -> G ⊢C raw_singleton x t -> G ⊢C ⊥.
Proof.
  intros Ht Hs. unfold raw_empty in Ht. finst Ht x.
  unfold raw_singleton in Hs. exact (IE Ht (CE1 Hs)).
Qed.

Lemma pair_not_empty G (HE : incl EqAx G) b t r :
  G ⊢C raw_empty t -> G ⊢C raw_pair b t r -> G ⊢C ¬ (r ≡' t).
Proof.
  intros Ht Hr. fintro E. unfold raw_empty in Ht. finst Ht b.
  apply (IE Ht). unfold raw_pair in Hr. pose proof (CE1 (CE1 Hr)) as Hbr. fmemE.
Qed.

Lemma pair_not_singleton G (HE : incl EqAx G) b t r x :
  G ⊢C ¬ (b ≡' t) -> G ⊢C raw_pair b t r -> G ⊢C ¬ (raw_singleton x r).
Proof.
  intros Hbt Hr. fintro Hs. unfold raw_pair in Hr. unfold raw_singleton in Hs.
  pose proof (CE1 (CE1 Hr)) as Hbr. pose proof (CE2 (CE1 Hr)) as Htr.
  pose proof (CE2 Hs) as Hb. finst Hb b. fmp Hb Hbr.
  pose proof (CE2 Hs) as Ht. finst Ht t. fmp Ht Htr.
  apply (IE Hbt). feqE.
Qed.
