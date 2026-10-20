(** Primitive labels for the independently checked AX position schedule.
    Metadata itself does not assert semantics; each actual history proof must
    check the labelled operation against its literal site. *)
From PAModel Require Import Program230AXPathSchedule.
From K230 Require Import RM RMEquiv.
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.
Inductive ax_primitive_op := APush | ALoad(r:nat) | AImplies | AIncrement(r:nat)
 | AUnpair(r:nat) | ATransfer(s t:nat) | ACopy2(s a b:nat).
Definition p230_ax_primitive_metadata:list(ax_primitive_op*nat):=[
(APush, 0);
 ((ALoad 4), 0);
 (APush, 1);
 ((ALoad 5), 1);
 (AImplies, 0);
 ((AIncrement 1), 0);
 ((AIncrement 1), 0);
 ((AUnpair 8), 3);
 ((ATransfer 7 8), 0);
 ((ATransfer 6 5), 0);
 (APush, 2);
 ((ALoad 3), 2);
 (APush, 3);
 ((AUnpair 8), 4);
 ((ATransfer 7 8), 0);
 ((ATransfer 6 1), 0);
 (AImplies, 1);
 (APush, 4);
 ((ALoad 4), 3);
 (AImplies, 2);
 (APush, 5);
 ((ALoad 4), 4);
 (APush, 6);
 ((ALoad 3), 5);
 (AImplies, 3);
 (APush, 7);
 ((ALoad 5), 6);
 (APush, 8);
 ((ALoad 3), 7);
 (AImplies, 4);
 (AImplies, 5);
 (AImplies, 6);
 (APush, 9);
 ((ALoad 3), 8);
 (APush, 10);
 ((ALoad 4), 9);
 (AImplies, 7);
 ((AIncrement 1), 0);
 ((AIncrement 1), 0);
 ((AIncrement 1), 0);
 (APush, 11);
 ((ALoad 3), 10);
 (APush, 12);
 ((ALoad 5), 11);
 (AImplies, 8);
 ((AIncrement 1), 0);
 ((AIncrement 1), 0);
 ((AIncrement 1), 0);
 (APush, 13);
 ((ALoad 4), 12);
 (APush, 14);
 ((ALoad 5), 13);
 (AImplies, 9);
 ((AIncrement 1), 0);
 ((AIncrement 1), 0);
 ((AIncrement 1), 0);
 (AImplies, 10);
 (AImplies, 11);
 (APush, 15);
 ((ALoad 4), 14);
 (APush, 16);
 ((ALoad 4), 15);
 (APush, 17);
 ((ALoad 3), 16);
 (AImplies, 12);
 ((AIncrement 1), 0);
 ((AIncrement 1), 0);
 (APush, 18);
 ((AIncrement 1), 0);
 (AImplies, 13);
 (AImplies, 14);
 ((AIncrement 1), 0);
 ((AIncrement 1), 0);
 (APush, 19);
 ((AIncrement 1), 0);
 (AImplies, 15);
 (APush, 20);
 ((ALoad 3), 17);
 (AImplies, 16);
 (APush, 21);
 ((ALoad 3), 18);
 (APush, 22);
 ((ALoad 4), 19);
 (AImplies, 17);
 ((AIncrement 1), 0);
 ((AIncrement 1), 0);
 ((AIncrement 1), 0);
 (APush, 23);
 ((ALoad 3), 20);
 (APush, 24);
 ((ALoad 5), 21);
 (AImplies, 18);
 ((AIncrement 1), 0);
 (APush, 25);
 ((ALoad 4), 22);
 (APush, 26);
 ((ALoad 5), 23);
 (AImplies, 19);
 ((AIncrement 1), 0);
 (AImplies, 20);
 (AImplies, 21);
 (APush, 27);
 ((ALoad 4), 24);
 (APush, 28);
 ((ALoad 5), 25);
 (APush, 29);
 ((ALoad 3), 26);
 (AImplies, 22);
 ((AIncrement 1), 0);
 ((AIncrement 1), 0);
 (AImplies, 23);
 ((AIncrement 1), 0);
 ((AIncrement 1), 0);
 (APush, 30);
 ((ALoad 5), 27);
 (APush, 31);
 ((ALoad 4), 28);
 (APush, 32);
 ((ALoad 3), 29);
 (AImplies, 24);
 ((AIncrement 1), 0);
 ((AIncrement 1), 0);
 (AImplies, 25);
 ((AIncrement 1), 0);
 ((AIncrement 1), 0);
 (AImplies, 26);
 (APush, 33);
 ((ALoad 4), 30);
 (APush, 34);
 ((ALoad 5), 31);
 (AImplies, 27);
 ((AIncrement 1), 0);
 ((AIncrement 1), 0);
 ((AIncrement 1), 0);
 (APush, 35);
 ((ALoad 3), 32);
 (APush, 36);
 ((ALoad 4), 33);
 (AImplies, 28);
 ((AIncrement 1), 0);
 (APush, 37);
 ((ALoad 3), 34);
 (APush, 38);
 ((ALoad 5), 35);
 (AImplies, 29);
 ((AIncrement 1), 0);
 (AImplies, 30);
 (AImplies, 31);
 (APush, 39);
 ((ALoad 4), 36);
 (APush, 40);
 ((ALoad 5), 37);
 (APush, 41);
 ((ALoad 3), 38);
 (AImplies, 32);
 (AImplies, 33);
 ((AIncrement 1), 0);
 ((AIncrement 1), 0);
 (APush, 42);
 ((ALoad 4), 39);
 (APush, 43);
 ((ALoad 5), 40);
 (AImplies, 34);
 ((AIncrement 1), 0);
 ((AIncrement 1), 0);
 (APush, 44);
 ((ALoad 4), 41);
 (APush, 45);
 ((ALoad 3), 42);
 (AImplies, 35);
 ((AIncrement 1), 0);
 ((AIncrement 1), 0);
 (AImplies, 36);
 (AImplies, 37);
 (APush, 46);
 ((ALoad 4), 43);
 (APush, 47);
 ((ALoad 4), 44);
 (APush, 48);
 ((ALoad 5), 45);
 (AImplies, 38);
 ((AIncrement 1), 0);
 ((AIncrement 1), 0);
 ((AIncrement 1), 0);
 (APush, 49);
 ((AIncrement 1), 0);
 (AImplies, 39);
 (AImplies, 40);
 ((AIncrement 1), 0);
 ((AIncrement 1), 0);
 (APush, 50);
 ((AIncrement 1), 0);
 (AImplies, 41);
 (APush, 51);
 ((ALoad 3), 46);
 (APush, 52);
 ((ALoad 3), 47);
 (APush, 53);
 ((ALoad 5), 48);
 (APush, 54);
 ((ALoad 3), 49);
 (AImplies, 42);
 ((AIncrement 1), 0);
 (AImplies, 43);
 (APush, 55);
 ((ALoad 5), 50);
 (APush, 56);
 ((ALoad 5), 51);
 (APush, 57);
 ((ALoad 3), 52);
 (AImplies, 44);
 ((AIncrement 1), 0);
 (APush, 58);
 ((ALoad 4), 53);
 (APush, 59);
 ((ALoad 3), 54);
 (APush, 60);
 ((ALoad 4), 55);
 (APush, 61);
 ((ALoad 3), 56);
 (APush, 62);
 ((ALoad 3), 57);
 (APush, 63);
 ((ALoad 4), 58);
 (AImplies, 45);
 ((AIncrement 1), 0);
 (APush, 64);
 ((ALoad 3), 59);
 (APush, 65);
 ((ALoad 5), 60);
 (AImplies, 46);
 ((AIncrement 1), 0);
 (AImplies, 47);
 (AImplies, 48);
 ((AIncrement 1), 0);
 ((AIncrement 1), 0);
 (APush, 66);
 ((ALoad 5), 61);
 (APush, 67);
 ((ALoad 3), 62);
 (APush, 68);
 ((ALoad 5), 63);
 (APush, 69);
 ((ALoad 3), 64);
 (APush, 70);
 ((ALoad 5), 65);
 (APush, 71);
 ((ALoad 3), 66);
 (AImplies, 49);
 ((AIncrement 1), 0);
 (APush, 72);
 ((AIncrement 1), 0);
 (AImplies, 50);
 (AImplies, 51);
 (APush, 73);
 ((AIncrement 1), 0);
 (AImplies, 52);
 (APush, 74);
 ((AIncrement 1), 0);
 (AImplies, 53);
 (AImplies, 54);
 ((AIncrement 1), 0);
 ((AIncrement 1), 0);
 (APush, 75);
 ((AIncrement 1), 0);
 (AImplies, 55);
 (AImplies, 56);
 (AImplies, 57);
 ((AIncrement 1), 0);
 ((AIncrement 1), 0);
 (AImplies, 58);
 (AImplies, 59);
 ((AIncrement 1), 0);
 ((AIncrement 1), 0);
 (APush, 76);
 ((AIncrement 1), 0);
 (AImplies, 60);
 (AImplies, 61);
 (APush, 77);
 ((AIncrement 1), 0);
 (AImplies, 62);
 (APush, 78);
 ((AIncrement 1), 0);
 (AImplies, 63);
 (AImplies, 64);
 ((AIncrement 1), 0);
 ((AIncrement 1), 0);
 (APush, 79);
 ((AIncrement 1), 0);
 (AImplies, 65);
 (AImplies, 66);
 (AImplies, 67);
 ((AIncrement 1), 0);
 ((AIncrement 1), 0);
 (APush, 80);
 ((AIncrement 1), 0);
 (AImplies, 68);
 (AImplies, 69);
 (APush, 81);
 ((AIncrement 1), 0);
 (AImplies, 70);
 (APush, 82);
 ((AIncrement 1), 0);
 (AImplies, 71);
 (AImplies, 72);
 ((AIncrement 1), 0);
 ((AIncrement 1), 0);
 (APush, 83);
 ((AIncrement 1), 0);
 (AImplies, 73);
 (APush, 84);
 ((ALoad 4), 67);
 (APush, 85);
 ((ALoad 5), 68);
 (AImplies, 74);
 ((AIncrement 1), 0);
 (APush, 86);
 ((ALoad 3), 69);
 (APush, 87);
 ((ALoad 4), 70);
 (APush, 88);
 ((ALoad 5), 71);
 (AImplies, 75);
 ((AIncrement 1), 0);
 (AImplies, 76);
 ((AIncrement 1), 0);
 ((AIncrement 1), 0);
 (AImplies, 77);
 (APush, 89);
 ((ALoad 4), 72);
 (APush, 90);
 ((ALoad 5), 73);
 (AImplies, 78);
 ((AIncrement 1), 0);
 ((AIncrement 1), 0);
 ((AIncrement 1), 0);
 (APush, 91);
 ((ALoad 3), 74);
 (APush, 92);
 ((ALoad 4), 75);
 (APush, 93);
 ((ALoad 5), 76);
 (AImplies, 79);
 ((AIncrement 1), 0);
 ((AIncrement 1), 0);
 ((AIncrement 1), 0);
 (AImplies, 80);
 ((AIncrement 1), 0);
 ((AIncrement 1), 0);
 (AImplies, 81);
 (APush, 94);
 ((AIncrement 1), 0);
 (AImplies, 82);
 (AImplies, 83);
 (APush, 95);
 ((AIncrement 1), 0);
 (AImplies, 84);
 (APush, 96);
 ((AIncrement 1), 0);
 (AImplies, 85);
 (AImplies, 86);
 (APush, 97);
 ((AIncrement 1), 0);
 (AImplies, 87)
].
Definition p230_ax_primitive_schedule := combine p230_ax_schedule p230_ax_primitive_metadata.
Definition ax_primitive_exit(item:(list bool*edge)*(ax_primitive_op*nat)):list bool:=
 let path:=fst(fst item) in
 match fst(snd item) with
 | APush=>inc_path(path++[true;true;true])
 | AImplies=>inc_path(path++[true;true])
 | ALoad _=>inc_path(path++[true])
 | _=>inc_path path end.
Definition ax_ipeqb(P Q:list bool):bool:=
 forallb(fun i => Bool.eqb(bit P i)(bit Q i))(seq 0 (Nat.max(length P)(length Q))).
Lemma ax_ipeqb_sound P Q:ax_ipeqb P Q=true->ipeq P Q.
Proof.
 intro H;unfold ax_ipeqb in H;unfold ipeq;intro i.
 destruct(lt_dec i(Nat.max(length P)(length Q)))as[Hi|Hi].
 -apply Bool.eqb_true_iff.
  apply (proj1(forallb_forall _ _)H);apply in_seq;lia.
 -unfold bit;rewrite !nth_overflow;try reflexivity;
  pose proof(Nat.le_max_l(length P)(length Q));
  pose proof(Nat.le_max_r(length P)(length Q));lia.
Qed.
Definition p230_ax_connector_rows :=
 combine p230_ax_primitive_schedule (tl(map fst p230_ax_schedule)++[p230_ax_schedule_gate]).
Theorem p230_ax_connectors_checked:
 forallb(fun item=>ax_ipeqb(ax_primitive_exit(fst item))(snd item))p230_ax_connector_rows=true.
Proof. vm_compute;reflexivity. Qed.
Theorem p230_ax_primitive_connectors:
 Forall(fun item=>ipeq(ax_primitive_exit(fst item))(snd item))p230_ax_connector_rows.
Proof.
 apply Forall_forall;intros item Hin;apply ax_ipeqb_sound.
 exact(proj1(forallb_forall _ _)p230_ax_connectors_checked item Hin).
Qed.
Theorem p230_ax_primitive_positions:
 map fst p230_ax_primitive_schedule=p230_ax_schedule.
Proof. vm_compute;reflexivity. Qed.
Theorem p230_ax_primitive_count:length p230_ax_primitive_schedule=364.
Proof. reflexivity. Qed.
Print Assumptions p230_ax_primitive_positions.
Print Assumptions p230_ax_primitive_count.
Print Assumptions ax_ipeqb_sound.
Print Assumptions p230_ax_connectors_checked.
Print Assumptions p230_ax_primitive_connectors.
