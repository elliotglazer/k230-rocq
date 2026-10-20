(** Translations of the canonical fixed ZF0 axioms. *)
From Coq Require Import Arith Lia List.
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_F Std_breq.
From OldK230S Require Import KP0 KP0Use KBase KMarkers KQuot KQuotMem KQuotExt KQuotFormula KQuotContext KQuotBasic KQuotSetUnion KQuotPower KPrimeTheory.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

(** The marker binder does not capture source free variables. *)
Definition qaxiom (phi : form) : form := ∀ (raw_empty $0 → qtrans $0 phi[↑]).

Theorem K0_qrefl : K0 ⊢TC qaxiom ax_refl'.
Proof.
  exists KLogic. split; [exact KLogic_ok|].
  assert (HL : incl KLogic KLogic) by (intros a Ha; exact Ha).
  unfold qaxiom. fall t.
  match goal with |- ?G ⊢C _ => assert (HL' : incl KLogic G) by exact HL end.
  fintro Hempty. cbn [qtrans ax_refl'].
  fall x. fintro Htx. exact (KLogic_refl _ HL' t x Hempty Htx).
Qed.

Theorem K0_qsym : K0 ⊢TC qaxiom ax_sym'.
Proof.
  exists KLogic. split; [exact KLogic_ok|].
  assert (HL : incl KLogic KLogic) by (intros a Ha; exact Ha).
  unfold qaxiom. fall t.
  match goal with |- ?G ⊢C _ => assert (HL' : incl KLogic G) by exact HL end.
  fintro Hempty. cbn [qtrans ax_sym'].
  fall x. fintro Htx. fall y. fintro Hty. fintro Hxy.
  exact (KLogic_sym _ HL' t x y Hempty Hxy).
Qed.

Theorem K0_qtrans : K0 ⊢TC qaxiom ax_trans'.
Proof.
  exists KLogic. split; [exact KLogic_ok|].
  assert (HL : incl KLogic KLogic) by (intros a Ha; exact Ha).
  unfold qaxiom. fall t.
  match goal with |- ?G ⊢C _ => assert (HL' : incl KLogic G) by exact HL end.
  fintro Hempty. cbn [qtrans ax_trans'].
  fall x. fintro Htx. fall y. fintro Hty. fall z. fintro Htz.
  fintro Hxy. fintro Hyz. exact (KLogic_trans _ HL' t x y z Hempty Hxy Hyz).
Qed.

Theorem K0_qeq_elem : K0 ⊢TC qaxiom ax_eq_elem'.
Proof.
  exists KLogic. split; [exact KLogic_ok|].
  assert (HL : incl KLogic KLogic) by (intros a Ha; exact Ha).
  unfold qaxiom. fall t.
  match goal with |- ?G ⊢C _ => assert (HL' : incl KLogic G) by exact HL end.
  fintro Hempty. cbn [qtrans ax_eq_elem'].
  fall x. fintro Htx. fall y. fintro Hty. fall x'. fintro Htx'. fall y'. fintro Hty'.
  fintro Hxx'. fintro Hyy'. fintro Hxy.
  pose proof (dmem_left _ (KLogic_base _ HL') t x x' y
    (KLogic_reverse _ HL') (KLogic_compose _ HL') Hempty Hxx' Hxy) as Hx'y.
  exact (dmem_right _ (KLogic_base _ HL') t x' y y'
    (KLogic_compose _ HL') Hempty Hyy' Hx'y).
Qed.

Theorem K0_qext : K0 ⊢TC qaxiom ax_ext'.
Proof.
  exists KExt. split; [exact KExt_ok|].
  assert (HK : incl KExt KExt) by (intros a Ha; exact Ha).
  unfold qaxiom. fall t.
  match goal with |- ?G ⊢C _ => assert (HK' : incl KExt G) by exact HK end.
  fintro Hempty. cbn [qtrans ax_ext' sub'].
  fall x. fintro Htx. fall y. fintro Hty. fintro Hxy. fintro Hyx.
  apply (KExt_ext _ HK' t x y Hempty Htx Hty).
  unfold same_dmembers. fall z. fintro Htz. fsplit.
  - fintro Hzx. finst Hxy z. fmp Hxy Htz. exact (IE Hxy Hzx).
  - fintro Hzy. finst Hyx z. fmp Hyx Htz. exact (IE Hyx Hzy).
Qed.

Theorem K0_qeset : K0 ⊢TC qaxiom ax_eset'.
Proof.
  destruct K0_proves_qempty as [B [HB H]]. exists B. split; [exact HB|].
  unfold qaxiom. fall t. fintro Hempty. unfold qempty_statement in H.
  finst H t. fmp H Hempty. unfold qempty in H. cbn [qtrans ax_eset' is_eset]. kconv H.
Qed.

Theorem K0_qpair : K0 ⊢TC qaxiom ax_pair'.
Proof.
  destruct K0_proves_qpair as [B [HB H]]. exists B. split; [exact HB|].
  unfold qaxiom. fall t. fintro Hempty. unfold qpair_statement in H.
  finst H t. cbn [qtrans ax_pair' is_pair].
  fall x. fintro Htx. fall y. fintro Hty.
  finst H x y. fmp H Hempty. fmp H Htx. fmp H Hty. unfold qpair in H. kconv H.
Qed.

Theorem K0_qunion : K0 ⊢TC qaxiom ax_union'.
Proof.
  destruct K0_proves_qunion as [B [HB H]]. exists B. split; [exact HB|].
  unfold qaxiom. fall t. fintro Hempty. unfold qunion_statement in H.
  finst H t. cbn [qtrans ax_union' is_union shift]. fall x. fintro Htx.
  finst H x. fmp H Hempty. fmp H Htx. unfold qunion in H. kconv H.
Qed.

Theorem K0_qpower : K0 ⊢TC qaxiom ax_power'.
Proof.
  destruct K0_proves_qpower as [B [HB H]]. exists B. split; [exact HB|].
  unfold qaxiom. fall t. fintro Hempty. unfold qpower_statement in H.
  finst H t. cbn [qtrans ax_power' is_power sub']. fall x. fintro Htx.
  finst H x. fmp H Hempty. fmp H Htx. unfold qpower, qsubset in H. kconv H.
Qed.

Theorem K0_qbase phi : In phi ZF0base -> K0 ⊢TC qaxiom phi.
Proof.
  intros H. destruct H as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]].
  - exact K0_qrefl.
  - exact K0_qsym.
  - exact K0_qtrans.
  - exact K0_qeq_elem.
  - exact K0_qext.
  - exact K0_qeset.
  - exact K0_qpair.
  - exact K0_qunion.
  - exact K0_qpower.
Qed.

Corollary KPrimeOrd_qbase phi : In phi ZF0base -> KPrimeOrd ⊢TC qaxiom phi.
Proof. intros H. apply K0_derivation_to_KPrimeOrd, K0_qbase, H. Qed.
