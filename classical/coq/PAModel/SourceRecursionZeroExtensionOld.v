(** Fixed zero-clause preservation when adjoining one recursion pair. *)
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_iface Std_setnd Std_setbase Std_setinf Std_setrec.
From PAModel Require Import SourceLFixed SourceHierarchyOld SourceRecursionFactsOld.
From Stdlib Require Import Lists.List.
Import ListNotations.
#[local] Existing Instance sig_empty |0.
#[local] Existing Instance ZF_pred_sig |0.
Unset Implicit Arguments.
Definition old_recursion_zero_clause o a f:form:=∀(App f`[↑] o`[↑] $0 →$0 ≡' a`[↑]).
Lemma old_recursion_zero_extension {G}(HG:incl ZF0base G)o a N f z next w q g:
 G ⊢C SNz phSig o N ->G ⊢C z ∈' N ->G ⊢C Rel2 phSig z next ->G ⊢C Adj f q g ->
 G ⊢C OP next w q ->G ⊢C old_recursion_zero_clause o a f ->G ⊢C old_recursion_zero_clause o a g.
Proof.
 intros HNZ HM HS HA HOP HZ. unfold old_recursion_zero_clause. fall v. fintro HApp.
 fhave Cases:(app_adj_el HG f q g o v HA HApp). fcases Cases HOld HNew.
 - unfold old_recursion_zero_clause in HZ. finst HZ v. exact(IE HZ HOld).
 - fhave EE:(op_inj HG o v next w q q HNew HOP(eq_refl' HG q)).
   pose proof(CE1 EE)as E. pose proof(eq_sym' HG o next E)as ER.
   frew_in ER(Rel2 phSig z`[↑] $0)HS.
   fabsurd. exact(snz_use phSig o N z HNZ HM HS).
Qed.
Definition old_recursion_zero_extension_law:form:=
 SNz phSig $0 $2 →$4 ∈' $2 →Rel2 phSig $4 $5 →Adj $3 $7 $8 →OP $5 $6 $7 →
 old_recursion_zero_clause $0 $1 $3 →old_recursion_zero_clause $0 $1 $8.
Theorem old_recursion_zero_extension_proof:old_L_background ⊢C old_recursion_zero_extension_law.
Proof.
 unfold old_recursion_zero_extension_law. do 6 apply II.
 eapply old_recursion_zero_extension;
 [recursion_fixed_background|recursion_fixed_context|recursion_fixed_context|recursion_fixed_context|
  recursion_fixed_context|recursion_fixed_context|recursion_fixed_context].
Qed.
Print Assumptions old_recursion_zero_extension.
Print Assumptions old_recursion_zero_extension_proof.
