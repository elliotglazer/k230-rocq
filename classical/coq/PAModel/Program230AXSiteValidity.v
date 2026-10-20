(** Every labelled primitive in the exact AX schedule has an actual verified
    catalogue entry or the literal transfer/increment shape required by its
    existing execution theorem. This adds semantics-relevant site coverage to
    the separate position and connector certificates. *)
From PAModel Require Import Program230AXPathSchedule Program230AXPrimitiveSchedule
 Program230PushSites Program230ParameterSites Program230ConsSites Program230UnpairSites
 Program230TransferProgram.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith.
Import ListNotations.
Unset Implicit Arguments.

Lemma ax_path_eqb_sound P Q:ax_path_eqb P Q=true->P=Q.
Proof.
 revert Q;induction P as[|p P IH];intros[|q Q];cbn;try discriminate;intro H;[reflexivity|].
 destruct p,q;cbn in H;try discriminate;f_equal;apply IH;exact H.
Qed.

Lemma ax_edge_eqb_sound e f:ax_edge_eqb e f=true->e=f.
Proof. destruct e,f;cbn;try discriminate;intro H;try(apply Nat.eqb_eq in H;now subst);reflexivity. Qed.

Definition ax_primitive_site_valid(item:(list bool*edge)*(ax_primitive_op*nat)):Prop:=
 let '(P,e):=fst item in let '(op,index):=snd item in
 match op with
 |APush=>match nth_error p230_push_site_rows index with
   |Some(Q,n)=>P=Q /\e=ENode n |None=>False end
 |ALoad r=>match nth_error p230_parameter_sites index with
   |Some site=>P=parameter_load site /\r=parameter_register site
   |None=>False end
 |AImplies=>match nth_error p230_cons_sites index with
   |Some site=>P=cons_path site /\e=ENode(cons_node site) |None=>False end
 |AUnpair r=>match nth_error p230_unpair_sites index with
   |Some(Q,a,n)=>P=Q /\r=a /\e=ENode n |None=>False end
 |AIncrement r=>e=EInc r
 |ATransfer a b=>match e with
   |ENode n=>program230_transfer_occurrence p230 P a b n (S n)
   |_=>False end
 |ACopy2 _ _ _=>False end.

Definition ax_primitive_site_validb(item:(list bool*edge)*(ax_primitive_op*nat)):bool:=
 let '(P,e):=fst item in let '(op,index):=snd item in
 match op with
 |APush=>match nth_error p230_push_site_rows index with
   |Some(Q,n)=>ax_path_eqb P Q && ax_edge_eqb e(ENode n) |None=>false end
 |ALoad r=>match nth_error p230_parameter_sites index with
   |Some site=>ax_path_eqb P(parameter_load site) && Nat.eqb r(parameter_register site)
   |None=>false end
 |AImplies=>match nth_error p230_cons_sites index with
   |Some site=>ax_path_eqb P(cons_path site) && ax_edge_eqb e(ENode(cons_node site)) |None=>false end
 |AUnpair r=>match nth_error p230_unpair_sites index with
   |Some(Q,a,n)=>ax_path_eqb P Q && (Nat.eqb r a && ax_edge_eqb e(ENode n)) |None=>false end
 |AIncrement r=>ax_edge_eqb e(EInc r)
 |ATransfer a b=>match e with
   |ENode n=>match fol p230(ENode(root p230))P with
     |Some actual=>let '(first,second):=nodes p230 n in
       let '(third,fourth):=nodes p230(S n) in
       ax_edge_eqb actual(ENode n) && (ax_edge_eqb first(EDecnz a) &&
       (ax_edge_eqb second(ENode(S n)) && (ax_edge_eqb third(EInc b) && ax_edge_eqb fourth(EContinue 2))))
     |None=>false end
   |_=>false end
 |ACopy2 _ _ _=>false end.

Theorem ax_primitive_site_validb_sound item:
 ax_primitive_site_validb item=true->ax_primitive_site_valid item.
Proof.
 destruct item as[[P e][op index]];destruct op;
  cbn [ax_primitive_site_validb ax_primitive_site_valid fst snd].
 -destruct(nth_error p230_push_site_rows index)as[[Q n]|];[|discriminate].
  rewrite andb_true_iff;intros[HP HE];split;[apply ax_path_eqb_sound|apply ax_edge_eqb_sound];assumption.
 -destruct(nth_error p230_parameter_sites index)as[site|];[|discriminate].
  rewrite andb_true_iff;intros[HP HE];split;[apply ax_path_eqb_sound|apply Nat.eqb_eq];assumption.
 -destruct(nth_error p230_cons_sites index)as[site|];[|discriminate].
  rewrite andb_true_iff;intros[HP HE];split;[apply ax_path_eqb_sound|apply ax_edge_eqb_sound];assumption.
 -apply ax_edge_eqb_sound.
 -destruct(nth_error p230_unpair_sites index)as[[[Q a] n]|];[|discriminate].
  rewrite !andb_true_iff;intros[HP[HA HE]];split;[apply ax_path_eqb_sound;exact HP|].
  split;[apply Nat.eqb_eq|apply ax_edge_eqb_sound];assumption.
 -destruct e as[n| | | | |];try discriminate.
  destruct(fol p230(ENode(root p230))P)as[actual|]eqn:HP;[|discriminate].
  destruct(nodes p230 n)as[first second]eqn:HN.
  destruct(nodes p230(S n))as[third fourth]eqn:HM.
  rewrite !andb_true_iff;intros[HE[HA[HB[HC HD]]]].
  apply ax_edge_eqb_sound in HE,HA,HB,HC,HD;subst actual first second third fourth.
  unfold program230_transfer_occurrence;split;[exact HP|]. split;assumption.
 -discriminate.
Qed.

Theorem p230_ax_primitive_site_check:
 forallb ax_primitive_site_validb p230_ax_primitive_schedule=true.
Proof. vm_compute;reflexivity. Qed.

Theorem p230_ax_primitive_sites_valid:
 Forall ax_primitive_site_valid p230_ax_primitive_schedule.
Proof.
 apply Forall_forall;intros item Hin;apply ax_primitive_site_validb_sound.
 exact(proj1(forallb_forall _ _)p230_ax_primitive_site_check item Hin).
Qed.

Print Assumptions ax_primitive_site_validb_sound.
Print Assumptions p230_ax_primitive_site_check.
Print Assumptions p230_ax_primitive_sites_valid.
