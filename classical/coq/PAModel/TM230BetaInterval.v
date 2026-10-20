(** The actual PA-definable beta-slice theorem, oriented for machine histories. *)
From PAModel Require Import Model Arithmetic FiniteCoding InternalPaths.
Unset Implicit Arguments.
Theorem machine230_beta_interval M b c offset count:exists db dc,
 forall i x,coding_lt M i count->
 (beta M b c(addM M offset i)x <->beta M db dc i x).
Proof.
 destruct(beta_slice M b c offset count)as[db[dc HP]].
 exists db,dc;intros i x Hi;symmetry;exact(HP i x Hi).
Qed.
Print Assumptions machine230_beta_interval.
