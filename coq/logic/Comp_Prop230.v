(** Retained calculus proof adapted from the pinned m254/Comp_Prop254.v. *)
(** * Comp_Prop230: propositional and first-order logic inside the code-level calculus thm230.

    [tau] maps the named wffs of Logic.v (O'Rear/Tarski S2 syntax, primitive negation) to codes,
    reading negation as implication to F = 1 = Rel(0,0):
        tau (Wn a) = wim (tau a) 1.
    Main result:  lprov a -> thm230 (tau a)   (every pure-logic theorem of Logic.v's S2).
    The propositional axioms come from the Lukasiewicz row rho8 (derivations in CD230.v, found by
    condensed detachment, zf/m230/logic/cdsearch.py) and from rho6 (explosion F -> b); the
    quantifier and equality axioms are rows rho1..rho7 literally; B6a is a projection of the bundle. *)
From Coq Require Import Arith Lia List.
From ZF Require Import Logic L1_LDef.
From K230L Require Import Codes230 Thm230 CD230.
Import ListNotations.

Fixpoint tau (a : wff) : nat :=
  match a with
  | Weq x y => weq x y
  | Wel x y => wel x y
  | Wim a b => wim (tau a) (tau b)
  | Wn a => wim (tau a) 1
  | Wal x a => wal x (tau a)
  end.

Lemma thm_I p : thm230 (wim p p).
Proof.
  exact (T_mp _ _ (thm_K p p) (T_mp _ _ (thm_K p (wim p p)) (thm_S p (wim p p) p))).
Qed.

(** ** Hilbert derivations with hypotheses, deduction theorem *)
Inductive der230 (G : list nat) : nat -> Prop :=
  | dhyp n : In n G -> der230 G n
  | dthm n : thm230 n -> der230 G n
  | dmp a b : der230 G (wim a b) -> der230 G a -> der230 G b.

Lemma ded G h a : der230 (h :: G) a -> der230 G (wim h a).
Proof.
  induction 1 as [n [<-|Hn] | n Hn | a b _ IH1 _ IH2].
  - apply dthm. apply thm_I.
  - apply (dmp _ n); [apply dthm, thm_K | now apply dhyp].
  - apply (dmp _ n); [apply dthm, thm_K | now apply dthm].
  - apply (dmp _ (wim h a)); [|exact IH2].
    apply (dmp _ (wim h (wim a b))); [apply dthm, thm_S | exact IH1].
Qed.

Lemma der_thm a : der230 [] a -> thm230 a.
Proof.
  induction 1 as [n [] | n Hn | a b _ IH1 _ IH2]; [exact Hn | exact (T_mp _ _ IH2 IH1)].
Qed.

Lemma der_weak G G' a : der230 G a -> incl G G' -> der230 G' a.
Proof.
  intros Hd Hi. induction Hd as [n Hn | n Hn | x y _ IH1 _ IH2];
    [apply dhyp; auto | now apply dthm | eapply dmp; eauto].
Qed.

Ltac hyp := apply dhyp; simpl; tauto.

(** ** Explosion and classical propositional logic *)
Lemma thm_F a : thm230 (wim 1 a).
Proof.
  (* rho6 0 a : (E.0 A.0 a) -> a,  and  F -> E.0 A.0 a  by K *)
  apply der_thm. apply ded.
  apply (dmp _ (wex 0 (wal 0 a))); [apply dthm, T_r6|].
  unfold wex, wn. apply (dmp _ 1); [apply dthm, thm_K | hyp].
Qed.

Lemma thm_DNE a : thm230 (wim (wim (wim a 1) 1) a).
Proof.
  (* Peirce ((a -> F) -> a) -> a,  and  ((a->F)->F) -> ((a->F) -> a) *)
  apply der_thm. apply ded.
  apply (dmp _ (wim (wim a 1) a)); [apply dthm, thm_P|].
  apply ded. apply (dmp _ 1); [apply dthm, thm_F|].
  apply (dmp _ (wim a 1)); hyp.
Qed.

(** ** Conjunction (wa a b = (a -> (b -> F)) -> F) *)
Lemma der_andl G a b : der230 G (wa a b) -> der230 G a.
Proof.
  intro H. apply (dmp _ (wim (wim a 1) 1)); [apply dthm, thm_DNE|].
  apply ded. apply (dmp _ (wim a (wn b))); [apply (der_weak _ _ _ H); intros ? ?; simpl; tauto|].
  apply ded. apply (dmp _ 1); [apply dthm, thm_F|]. apply (dmp _ a); hyp.
Qed.

Lemma der_andr G a b : der230 G (wa a b) -> der230 G b.
Proof.
  intro H. apply (dmp _ (wim (wim b 1) 1)); [apply dthm, thm_DNE|].
  apply ded. apply (dmp _ (wim a (wn b))); [apply (der_weak _ _ _ H); intros ? ?; simpl; tauto|].
  apply ded. hyp.
Qed.

Lemma der_andi G a b : der230 G a -> der230 G b -> der230 G (wa a b).
Proof.
  intros Ha Hb. unfold wa, wn. apply ded.
  apply (dmp _ b); [|apply (der_weak _ _ _ Hb); intros ? ?; simpl; tauto].
  apply (dmp _ a); [hyp | apply (der_weak _ _ _ Ha); intros ? ?; simpl; tauto].
Qed.

(** ** The lprov axioms *)
Lemma thm_B3 a b : thm230 (wim a (wim (wim a 1) b)).
Proof.
  apply der_thm. do 2 apply ded.
  apply (dmp _ 1); [apply dthm, thm_F|]. apply (dmp _ a); hyp.
Qed.

Lemma thm_B6a x y z : x <> z -> y <> z ->
  thm230 (wa (wim (weq x y) (wal z (weq x y))) (wim (wel x y) (wal z (wel x y)))).
Proof.
  intros H1 H2. pose proof (T_bundle x y z (not_eq_sym H1) (not_eq_sym H2)) as HB.
  unfold bundle in HB. apply der_thm.
  assert (V : der230 [] (wa (wim (wel x y) (wal z (wel x y))) (wim (weq x y) (wal z (weq x y)))))
    by (eapply der_andr; apply dthm; exact HB).
  apply der_andi; [eapply der_andr | eapply der_andl]; exact V.
Qed.

Theorem lprov_thm a : lprov a -> thm230 (tau a).
Proof.
  induction 1 as [a b _ IH1 _ IH2 | x a _ IH | a b c | a | a b | x a b | x y z Hxz Hyz
                  | x y a | x a | x y | x y z | x y z | x y z]; cbn [tau].
  - exact (T_mp _ _ IH2 IH1).
  - now apply T_gen.
  - apply thm_B.
  - apply thm_P.
  - apply thm_B3.
  - apply T_r2.
  - now apply thm_B6a.
  - apply T_r4.
  - apply (T_r6 x (tau a)).
  - apply (T_r1 x y).
  - apply (T_r7 y z x).
  - apply (T_r5 y z x).
  - apply (T_r3 x y z).
Qed.
