(** Adapted from the pinned m254/L1_254.v; same command calculus with K230 bundle. *)
(** * L1_230: the abstract enumerator of the zfc_230 source halts iff the code-level calculus
    derives the code 1 (= F = Rel(0,0) = v0 e. v0). *)
From K230L Require Import Enum230 Thm230 L1_Sound230 L1_Comp230.

Theorem L1_230 : enum230_halts <-> thm230 1.
Proof. split; [exact enum_sound | exact enum_complete]. Qed.

Print Assumptions L1_230.
