(** A genuinely fixed Separation instance for recursion-attempt agreement. *)
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_iface Std_setnd Std_setbase Std_setrec.
From OldZFC Require Import Z_base Z_prim Z_rel.
From PAModel Require Import SourceLFixed SourceLNonempty.
From Stdlib Require Import Lists.List.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.
Definition old_agreement_separation_axiom:=forall_times 2(ax_sep' agr_form).
Definition old_agreement_separation_background:=old_agreement_separation_axiom::old_L_background.
Definition old_agreement_separation_law:form:=∃∀($0 ∈' $1 ↔($0 ∈' $4 ∧Agr $2 $3 $0)).
Theorem old_agreement_separation_background_valid a:In a old_agreement_separation_background ->ZFR a.
Proof.
 intros[<-|HA];[apply ZFR_sep;exact fb_agr|exact(old_L_background_valid a HA)].
Qed.
Theorem old_agreement_separation_proof:old_agreement_separation_background ⊢C old_agreement_separation_law.
Proof.
 pose proof(sep_use old_agreement_separation_background 2 agr_form($0.:$1.:var)$2(or_introl eq_refl)fb_agr)as H.
 unfold agr_form in H. simp_in H. exact H.
Qed.
Print Assumptions old_agreement_separation_background_valid.
Print Assumptions old_agreement_separation_proof.
