(** Exact register pairs of every transfer in the checked native AX trace. *)
From PAModel Require Import Program230AXNativeSymbolic Program230AXSymbolicTrace Program230AXTypedNormalization.
From Stdlib Require Import Lists.List Arith.Arith Bool.Bool Lia.
Import ListNotations.
Unset Implicit Arguments.
Definition p230_ax_transfer_pair(a b:nat):Prop:=(a=7 /\b=8) \/(a=6 /\b=5) \/(a=6 /\b=1).
Definition p230_ax_transfer_pairb(a b:nat):bool:=
 (Nat.eqb a 7 &&Nat.eqb b 8)||(Nat.eqb a 6 &&(Nat.eqb b 5||Nat.eqb b 1)).
Lemma p230_ax_transfer_pairb_sound a b:p230_ax_transfer_pairb a b=true->p230_ax_transfer_pair a b.
Proof.
 unfold p230_ax_transfer_pairb,p230_ax_transfer_pair;intro H.
 apply Bool.orb_true_iff in H;destruct H as[H|H].
 -apply Bool.andb_true_iff in H;destruct H as[HA HB];apply Nat.eqb_eq in HA;apply Nat.eqb_eq in HB;auto.
 -apply Bool.andb_true_iff in H;destruct H as[HA HB];apply Nat.eqb_eq in HA.
  apply Bool.orb_true_iff in HB;destruct HB as[HB|HB];apply Nat.eqb_eq in HB;auto.
Qed.
Definition p230_ax_transfer_rowb(row:p230_ax_native_row):bool:=
 let '(op,_,_):=row in match op with ANTransfer a b=>p230_ax_transfer_pairb a b|_=>true end.
Theorem p230_ax_native_transfer_pairs:
 Forall(fun row=>let '(op,_,_):=row in match op with ANTransfer a b=>p230_ax_transfer_pair a b|_=>True end)p230_ax_native_rows.
Proof.
 assert(H:forallb p230_ax_transfer_rowb p230_ax_native_rows=true)by(vm_compute;reflexivity).
 apply Forall_forall;intros[[op before]after]HI.
 pose proof(proj1(forallb_forall _ _)H _ HI)as HB.
 destruct op;try exact I;apply p230_ax_transfer_pairb_sound;exact HB.
Qed.
Lemma p230_ax_typed_transfer_check:
 forallb(fun row=>p230_ax_transfer_rowb(snd row))p230_ax_typed_rows=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque p230_ax_native_rows p230_ax_typed_rows.
Theorem p230_ax_typed_transfer_pairs item a b before after:
 In(item,(ANTransfer a b,before,after))p230_ax_typed_rows->p230_ax_transfer_pair a b.
Proof.
 intro H;apply p230_ax_transfer_pairb_sound.
 exact(proj1(forallb_forall _ _)p230_ax_typed_transfer_check _ H).
Qed.
Theorem p230_ax_typed_transfer_bounds item a b before after:
 In(item,(ANTransfer a b,before,after))p230_ax_typed_rows->(a<9)%nat /\(b<9)%nat /\a<>b.
Proof.
 intro H;pose proof(p230_ax_typed_transfer_pairs item a b before after H)as HE.
 unfold p230_ax_transfer_pair in HE;destruct HE as[[HA HB]|[[HA HB]|[HA HB]]];subst;repeat split;lia.
Qed.
Print Assumptions p230_ax_native_transfer_pairs.
Print Assumptions p230_ax_typed_transfer_pairs.
Print Assumptions p230_ax_typed_transfer_bounds.
