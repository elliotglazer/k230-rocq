From Coq Require Import Arith Lia List.
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Logic Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_F Std_breq Std_glue.
From OldK230S Require Import KP0 KBase KMarkers KQuot KQuotFormula.
From OldK230L Require Import Codes230 Thm230 Comp_Prop230.
From OldFixedTarget Require Import Positive230.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.
Local Opaque KCode230.P.

Definition raw_member_intro_body : form := raw_empty $2 → $2 ∈' $1 → $1 ∈' $0 → dmem $2 $1 $0.
Definition raw_member_intro_source : form := forall_times 3 raw_member_intro_body.
Definition raw_member_intro_code := tau (tr eta0 raw_member_intro_source).

Theorem K0_raw_member_intro : K0 ⊢TC raw_member_intro_source.
Proof.
  exists KLogic. split;[exact KLogic_ok|].
  assert (HL : incl KLogic KLogic) by (intros f HF;exact HF).
  unfold raw_member_intro_source,raw_member_intro_body;cbn [forall_times].
  fall t. fall x. fall y.
  match goal with |- ?G ⊢C _ => assert (HL' : incl KLogic G) by exact HL end.
  fintro HE. fintro HD. fintro HM.
  unfold dmem. fexists x. fsplit.
  - unfold dchild. fsplit;assumption.
  - exact (KLogic_refl _ HL' t x HE HD).
Qed.

Theorem original_raw_member_intro_certificate : thm230 raw_member_intro_code.
Proof. exact (K0_to_positive_formula _ eta0 K0_raw_member_intro oddenv_eta0). Qed.

Print Assumptions K0_raw_member_intro.
Print Assumptions original_raw_member_intro_certificate.
