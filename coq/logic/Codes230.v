(** Retained logical rows copied from the pinned m254 code calculus.
    The source bundle is K230's exact checked code, not m254's set theory. *)
From Coq Require Import Arith Lia.
From K230S Require Export KCode230.
Definition rho8 (a b c u : nat) : nat := wim (wim (wim c u) a) (wim (wim a c) (wim b c)).  (* L *)
Definition rho7 (a b c : nat) : nat := wim (weq c a) (wim (weq c b) (weq a b)).          (* Euclid *)
Definition rho6 (a b : nat) : nat := wim (wex a (wal a b)) b.                            (* B6c *)
Definition rho5 (a b c : nat) : nat := wim (weq c a) (wim (wel c b) (wel a b)).          (* cong left *)
Definition rho4 (a b c : nat) : nat := wim (wal a (wal b c)) (wal b (wal a c)).          (* commutation *)
Definition rho3 (a b c : nat) : nat := wim (weq a b) (wim (wel c a) (wel c b)).          (* cong right *)
Definition rho2 (a b c : nat) : nat := wim (wal a (wim b c)) (wim (wal a b) (wal a c)).  (* QI *)
Definition rho1 (a b : nat) : nat := wex a (weq a b).                                    (* E.a a=b *)


Definition bundle := bundle230.
Lemma bundle_ne_F a b c : bundle a b c <> F.
Proof. apply bundle230_ne_halt. Qed.
