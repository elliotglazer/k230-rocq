(** Only registers 0 through 8 are observed by the numerical leaf semantics.
    Agreement at those coordinates suffices; no function extensionality is used. *)
From PAModel Require Import Model Arithmetic Program230Edges Program230Transition.
From K230 Require Import RM RMEquiv.
From Stdlib Require Import Arith.Arith Bool.Bool.
Unset Implicit Arguments.

Lemma program230_register_same_transport M (R T R' T':nat->carrier M) :
 (forall i,(i<9)%nat->R i=R' i) ->
 (forall i,(i<9)%nat->T i=T' i) ->
 program230_register_same M R T ->program230_register_same M R' T'.
Proof.
 intros HR HT HS i Hi. rewrite <-(HT i Hi),<-(HR i Hi). exact (HS i Hi).
Qed.

Lemma program230_register_update_transport M r value (R T R' T':nat->carrier M) :
 (forall i,(i<9)%nat->R i=R' i) ->
 (forall i,(i<9)%nat->T i=T' i) ->
 program230_register_update M r value R T ->program230_register_update M r value R' T'.
Proof.
 intros HR HT HU i Hi. rewrite <-(HT i Hi).
 specialize (HU i Hi). destruct (Nat.eqb i r);[exact HU|].
 rewrite <-(HR i Hi);exact HU.
Qed.

Lemma program230_edge_register_transport M Q e (R T R' T':nat->carrier M) pc' :
 (forall i,(i<9)%nat->R i=R' i) ->
 (forall i,(i<9)%nat->T i=T' i) ->
 program230_edge_step M Q e R T pc' ->program230_edge_step M Q e R' T' pc'.
Proof.
 intros HR HT. destruct e as[n|r|r|k|k|];cbn[program230_edge_step];intro HE.
 -exact HE.
 -destruct HE as [Hr [Hp HU]]. split;[exact Hr|split;[exact Hp|]].
  rewrite (HR r Hr) in HU.
  exact (program230_register_update_transport M r _ R T R' T' HR HT HU).
 -destruct HE as [Hr HE]. split;[exact Hr|].
  destruct HE as [[HZ [Hp HS]]|[v [HV [Hp HU]]]].
  +left;split;[rewrite <-(HR r Hr);exact HZ|split;[exact Hp|]].
   exact (program230_register_same_transport M R T R' T' HR HT HS).
  +right;exists v;split;[rewrite <-(HR r Hr);exact HV|split;[exact Hp|]].
   exact (program230_register_update_transport M r v R T R' T' HR HT HU).
 -destruct HE as [Hp HS];split;[exact Hp|].
  exact (program230_register_same_transport M R T R' T' HR HT HS).
 -destruct HE as [Hp HS];split;[exact Hp|].
  exact (program230_register_same_transport M R T R' T' HR HT HS).
 -exact HE.
Qed.

Theorem program230_edge_register_extensional M Q e (R T R' T':nat->carrier M) pc' :
 (forall i,(i<9)%nat->R i=R' i) ->
 (forall i,(i<9)%nat->T i=T' i) ->
 (program230_edge_step M Q e R T pc' <->program230_edge_step M Q e R' T' pc').
Proof.
 intros HR HT;split.
 -exact (program230_edge_register_transport M Q e R T R' T' pc' HR HT).
 -apply (program230_edge_register_transport M Q e R' T' R T pc').
  +intros i Hi;symmetry;exact (HR i Hi).
  +intros i Hi;symmetry;exact (HT i Hi).
Qed.

Theorem program230_step_register_extensional M p pc (R T R' T':nat->carrier M) pc' :
 (forall i,(i<9)%nat->R i=R' i) ->
 (forall i,(i<9)%nat->T i=T' i) ->
 (program230_step M p pc R T pc' <->program230_step M p pc R' T' pc').
Proof.
 intros HR HT;split;intros [e [Q [rest [HW HE]]]];exists e,Q,rest;split;[exact HW| |exact HW|].
 -apply (proj1 (program230_edge_register_extensional M Q e R T R' T' pc' HR HT));exact HE.
 -apply (proj2 (program230_edge_register_extensional M Q e R T R' T' pc' HR HT));exact HE.
Qed.

Print Assumptions program230_register_same_transport.
Print Assumptions program230_register_update_transport.
Print Assumptions program230_edge_register_extensional.
Print Assumptions program230_step_register_extensional.
