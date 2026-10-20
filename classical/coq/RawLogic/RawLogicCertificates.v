(** Four closed raw quotient laws, proved from the actual K0/KLogic axioms. *)
From Coq Require Import Arith Lia List.
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Logic Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_F Std_breq Std_glue.
From OldK230S Require Import KP0 KBase KMarkers KQuot KQuotSym KQuotTrans KQuotMem KQuotFormula.
From OldK230L Require Import Codes230 Thm230 Comp_Prop230.
From OldFixedTarget Require Import Positive230.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.
Local Opaque KCode230.P.

Inductive raw_law := RawSymmetry | RawTransitivity | RawLeft | RawRight.
Definition raw_law_arity law := match law with RawSymmetry=>3 | _=>4 end.
Definition raw_law_body law : form :=
  match law with
  | RawSymmetry => raw_empty $2 → deqv $2 $1 $0 → deqv $2 $0 $1
  | RawTransitivity => raw_empty $3 → deqv $3 $2 $1 → deqv $3 $1 $0 → deqv $3 $2 $0
  | RawLeft => raw_empty $3 → deqv $3 $2 $1 → dmem $3 $2 $0 → dmem $3 $1 $0
  | RawRight => raw_empty $3 → deqv $3 $1 $0 → dmem $3 $2 $1 → dmem $3 $2 $0
  end.
Definition raw_law_source law := forall_times (raw_law_arity law) (raw_law_body law).
Definition raw_law_code law := tau (tr eta0 (raw_law_source law)).

Theorem K0_raw_left : K0 ⊢TC raw_law_source RawLeft.
Proof.
  exists KLogic. split;[exact KLogic_ok|].
  assert (HL : incl KLogic KLogic) by (intros a Ha;exact Ha).
  unfold raw_law_source,raw_law_arity,raw_law_body;cbn [forall_times].
  fall t. fall x. fall x'. fall y.
  match goal with |- ?G ⊢C _ => assert (HL' : incl KLogic G) by exact HL end.
  fintro HE. fintro HH. fintro HM.
  exact (dmem_left _ (KLogic_base _ HL') t x x' y
    (KLogic_reverse _ HL') (KLogic_compose _ HL') HE HH HM).
Qed.

Theorem K0_raw_right : K0 ⊢TC raw_law_source RawRight.
Proof.
  exists KLogic. split;[exact KLogic_ok|].
  assert (HL : incl KLogic KLogic) by (intros a Ha;exact Ha).
  unfold raw_law_source,raw_law_arity,raw_law_body;cbn [forall_times].
  fall t. fall x. fall y. fall y'.
  match goal with |- ?G ⊢C _ => assert (HL' : incl KLogic G) by exact HL end.
  fintro HE. fintro HH. fintro HM.
  exact (dmem_right _ (KLogic_base _ HL') t x y y'
    (KLogic_compose _ HL') HE HH HM).
Qed.

Theorem K0_raw_law law : K0 ⊢TC raw_law_source law.
Proof.
  destruct law.
  - exact K0_proves_deqv_sym.
  - exact K0_proves_deqv_trans.
  - exact K0_raw_left.
  - exact K0_raw_right.
Qed.

Theorem original_raw_law_certificate law : thm230 (raw_law_code law).
Proof. exact (K0_to_positive_formula _ eta0 (K0_raw_law law) oddenv_eta0). Qed.

Print Assumptions K0_raw_left.
Print Assumptions K0_raw_right.
Print Assumptions K0_raw_law.
Print Assumptions original_raw_law_certificate.
