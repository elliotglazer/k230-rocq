(** * Std_iface2: bridges between O'Rear's axioms and the library's, as ND obligations.

    [Lib n a] = the library closure of the named wff [a] (with [maxfr a < n]):
      dB var (A. v_(n-1) ... A. v_0 a), a closed library formula.
    [TPset] = the closures of all [prov]-theorems.  Every element translates back to a prov-theorem
    (Std_gen.tr_cl_prov), so derivations from [TPset] are sound for [prov] (Std_H.nd_sound).

    Obligations (classical ND, closed hypotheses):
      [bridge_ZF0]  : every ZF0 axiom is derivable from TPset
      [bridge_INF]  : INF_lib is derivable from TPset
      [bridge_EXT] [bridge_POW] [bridge_UNI] [bridge_REP] [bridge_INFo] :
                      the closures of O'Rear's axioms are derivable from ZFc            *)
From Coq Require Import Arith Lia List Bool.
From OldUndecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Logic L1_LDef L1_LProp L1_LMeta Std_dB Std_tr Std_alpha Std_gen Std_iface.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Definition Lib (n : nat) (a : wff) : form := dB var (genall n a).

Definition TPset (th : form) : Prop := exists a n, prov a /\ maxfr a < n /\ th = Lib n a.

Lemma Lib_closed n a : maxfr a < n -> closedf (Lib n a).
Proof. apply fb_cl. Qed.

Lemma TPset_closed th : TPset th -> closedf th.
Proof. intros (a & n & _ & Hn & ->). now apply Lib_closed. Qed.

Lemma TPset_Lib n a : prov a -> maxfr a < n -> TPset (Lib n a).
Proof. intros. exists a, n. auto. Qed.

(** instantiate a closure at arbitrary terms *)
Lemma Lib_inst A n a (sigma : nat -> term) : maxfr a < n -> A ⊢C Lib n a -> A ⊢C dB sigma a.
Proof. intros Hn H. exact (gen_inst_full A n a var sigma Hn H). Qed.

Definition bridge_ZF0 : Prop := forall psi, ZF0 psi -> thm TPset psi.
Definition bridge_INF : Prop := thm TPset INF_lib.

(* [maxfr] over-approximates the free variables (it counts every variable of every atom), so the
   closures below also quantify (vacuously) over bound names. *)
Definition bridge_EXT : Prop := thm ZFc (Lib 3 EXT).
Definition bridge_POW : Prop := thm ZFc (Lib 4 POW).
Definition bridge_UNI : Prop := thm ZFc (Lib 4 UNI).
Definition bridge_INFo : Prop := thm ZFc (Lib 3 INF).
Definition bridge_REP : Prop := forall ph n, maxfr (REP ph) < n -> thm ZFc (Lib n (REP ph)).

Lemma maxfr_EXT : maxfr EXT < 3.  Proof. cbv; lia. Qed.
Lemma maxfr_POW : maxfr POW < 4.  Proof. cbv; lia. Qed.
Lemma maxfr_UNI : maxfr UNI < 4.  Proof. cbv; lia. Qed.
Lemma maxfr_INF : maxfr INF < 3.  Proof. cbv; lia. Qed.
