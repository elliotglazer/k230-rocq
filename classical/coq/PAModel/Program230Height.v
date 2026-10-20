(** The literal p230 height certificate bounds every control walk by 40.
    Only the 5124 table rows are checked. No path tree is expanded. *)
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.

Definition program230_height_row (n:nat):bool :=
 (hE (lk p230_H) (fst (nodes p230 n)) <? lk p230_H n) &&
 (hE (lk p230_H) (snd (nodes p230 n)) <? lk p230_H n).

Lemma program230_height_table_checked :
 forallb program230_height_row (seq 0 (nnodes p230))=true.
Proof. vm_compute. reflexivity. Qed.

Lemma program230_height_decreases n b : n<nnodes p230 ->
 hE (lk p230_H) (child p230 n b)<lk p230_H n.
Proof.
 intros Hn. pose proof program230_height_table_checked as HC.
 rewrite forallb_forall in HC.
 specialize (HC n ltac:(apply in_seq;lia)).
 unfold program230_height_row in HC. apply andb_true_iff in HC as [HL HR].
 unfold child;destruct b;apply Nat.ltb_lt;assumption.
Qed.

Lemma program230_root_height : lk p230_H (root p230)=40.
Proof. reflexivity. Qed.

Lemma program230_walk_height_bound p (W:wf p) H
 (HH:forall n b,n<nnodes p ->hE H(child p n b)<H n)
 fuel n P i e d : n<nnodes p ->
 walk p fuel n P i=Some(e,d) ->d<=i+H n.
Proof.
 revert n i. induction fuel as [|fuel IH];intros n i Hn HW;[discriminate|].
 rewrite walk_S in HW.
 pose proof (HH n (bit P i) Hn) as HD.
 pose proof (wf_edges p W n (bit P i) Hn) as HE.
 destruct (child p n (bit P i)) as [m|r|r|k|k|] eqn:HC.
 2-6:injection HW as _ <-;cbn [hE] in HD;lia.
 cbn [hE] in HD. cbn [edge_ok] in HE.
 specialize (IH m (S i) HE HW). lia.
Qed.

Lemma program230_walk_fuel_deterministic p f g n P i e d e' d' :
 walk p f n P i=Some(e,d) ->walk p g n P i=Some(e',d') ->
 e=e' /\ d=d'.
Proof.
 revert g n i. induction f as [|f IH];intros g n i HF HG;[discriminate|].
 destruct g as [|g];[discriminate|]. rewrite walk_S in HF,HG.
 destruct (child p n (bit P i)) as [m|r|r|k|k|].
 2-6:injection HF as <- <-;injection HG as <- <-;split;reflexivity.
 eapply IH;eassumption.
Qed.

Theorem program230_walk_depth_40 fuel P e d :
 walk p230 fuel (root p230) P 0=Some(e,d) ->d<=40.
Proof.
 intros HW. pose proof (program230_walk_height_bound p230 p230_wf
  (lk p230_H) program230_height_decreases fuel (root p230) P 0 e d
  (wf_root p230 p230_wf) HW) as HD.
 rewrite program230_root_height in HD. exact HD.
Qed.

Theorem program230_walk_40_total P :
 exists e d,walk p230 40 (root p230) P 0=Some(e,d).
Proof.
 apply (walk_some p230 p230_wf (lk p230_H) program230_height_decreases).
 -exact (wf_root p230 p230_wf).
 -rewrite program230_root_height;lia.
Qed.

Theorem program230_walk_40_exact P e d :
 walk p230 (nnodes p230+1) (root p230) P 0=Some(e,d) <->
 walk p230 40 (root p230) P 0=Some(e,d).
Proof.
 split;intro HW.
 -destruct (program230_walk_40_total P) as [e' [d' HE]].
  destruct (program230_walk_fuel_deterministic p230 _ _ _ _ _ _ _ _ _ HW HE)
   as [-> ->];exact HE.
 -destruct (wf_walk p230 p230_wf P) as [e' [d' HE]].
  destruct (program230_walk_fuel_deterministic p230 _ _ _ _ _ _ _ _ _ HW HE)
   as [-> ->];exact HE.
Qed.

Print Assumptions program230_height_decreases.
Print Assumptions program230_walk_depth_40.
Print Assumptions program230_walk_40_total.
Print Assumptions program230_walk_40_exact.
