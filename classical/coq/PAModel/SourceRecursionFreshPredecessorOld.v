(** Fixed predecessor transport in the fresh-pair branch of extension. *)
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_iface Std_setnd Std_setbase Std_setinf Std_setrec.
From PAModel Require Import SourceLFixed SourceRecursionFactsOld.
From Stdlib Require Import Lists.List.
Import ListNotations.
#[local] Existing Instance sig_empty |0.
#[local] Existing Instance ZF_pred_sig |0.
Unset Implicit Arguments.
Lemma old_recursion_fresh_predecessor {G}(HG:incl ZF0base G)N z next f v q g u nextu:
 G ⊢C SInj phSig N ->G ⊢C z ∈' N ->G ⊢C Rel2 phSig z next ->G ⊢C App f z v ->
 G ⊢C Adj f q g ->G ⊢C u ∈' N ->G ⊢C Rel2 phSig u nextu ->G ⊢C nextu ≡' next ->G ⊢C App g u v.
Proof.
 intros HInj HZ HZS HApp HAdj HU HUS ENext.
 frew_in ENext(Rel2 phSig u`[↑] $0)HUS.
 pose proof(sinj_use phSig N z u next HInj HZ HU HZS HUS)as EPre.
 frew_in EPre(App f`[↑] $0 v`[↑])HApp.
 exact(app_adj_l HG f q g u v HAdj HApp).
Qed.
Definition old_recursion_fresh_predecessor_law:form:=
 SInj phSig $0 →$1 ∈' $0 →Rel2 phSig $1 $2 →App $3 $1 $4 →Adj $3 $5 $6 →
 $7 ∈' $0 →Rel2 phSig $7 $8 →$8 ≡' $2 →App $6 $7 $4.
Theorem old_recursion_fresh_predecessor_proof:old_L_background ⊢C old_recursion_fresh_predecessor_law.
Proof.
 unfold old_recursion_fresh_predecessor_law. do 8 apply II.
 eapply old_recursion_fresh_predecessor with(N:=$0)(z:=$1)(next:=$2)(f:=$3)(v:=$4)(q:=$5)(g:=$6)(u:=$7)(nextu:=$8);
 [recursion_fixed_background|recursion_fixed_context|recursion_fixed_context|recursion_fixed_context|
  recursion_fixed_context|recursion_fixed_context|recursion_fixed_context|recursion_fixed_context|recursion_fixed_context].
Qed.
Print Assumptions old_recursion_fresh_predecessor.
Print Assumptions old_recursion_fresh_predecessor_proof.
