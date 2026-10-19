(** Adapted from the pinned m254/Thm254.v; same command calculus with K230 bundle. *)
(** * Thm230: the machine's calculus at the level of codes.

    [thm230 n]: n is derivable from the AX rows and gated bundles by MP and GEN, with the
    truth code 0 as an axiom (stack zeros, failed MP and failed gates produce 0).
    L1 proves  enum230_halts <-> thm230 1;  the bridge relates thm230 to the set theory SIR. *)
From Coq Require Import Arith Lia.
From K230L Require Import Codes230.

Inductive thm230 : nat -> Prop :=
  | T_true : thm230 0
  | T_mp t b : thm230 t -> thm230 (wim t b) -> thm230 b
  | T_gen a h : thm230 h -> thm230 (wal a h)
  | T_r1 a b : thm230 (rho1 a b)
  | T_r2 a b c : thm230 (rho2 a b c)
  | T_r3 a b c : thm230 (rho3 a b c)
  | T_r4 a b c : thm230 (rho4 a b c)
  | T_r5 a b c : thm230 (rho5 a b c)
  | T_r6 a b : thm230 (rho6 a b)
  | T_r7 a b c : thm230 (rho7 a b c)
  | T_r8 a b c u : thm230 (rho8 a b c u)
  | T_bundle a b c : c <> a -> c <> b -> thm230 (bundle a b c).
