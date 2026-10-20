(** Composing a genuine compiled block with actual search entry and histories. *)
From PAModel Require Import Model SearchStep KernelSafety RunSyntax NumericalReachability
 NumericalSearchDrain ProgramRealizability NumericalCandidateEntry.
Unset Implicit Arguments.

Theorem numerical_seed_executes_block M f tail p :
 program_block M f tail p ->
 numerical_halts_from M(seed_state M) \/
 exists candidate w,numerical_reaches M(seed_state M)
  (mkSearchState(carrier M)tail(succM M candidate)f w(zeroM M)(zeroM M)).
Proof.
 intro Hp. destruct(numerical_seed_enters_program M p)as[Hhalt|[c[t[w[Hcode Hreach]]]]].
 - now left.
 - destruct(Hp(succM M c)t w)as[Hhalt|Hblock].
   + left. exact(numerical_reaches_halts M _ _ Hreach Hhalt).
   + right. exists c,w. exact(numerical_reaches_transitive M _ _ _ Hreach Hblock).
Qed.
Theorem numerical_seed_executes_realized M f tail :
 program_realizes M f ->
 numerical_halts_from M(seed_state M) \/
 exists candidate w,numerical_reaches M(seed_state M)
  (mkSearchState(carrier M)tail(succM M candidate)f w(zeroM M)(zeroM M)).
Proof.
 intro H. destruct(H tail)as[p Hp]. exact(numerical_seed_executes_block M f tail p Hp).
Qed.
Print Assumptions numerical_seed_executes_block.
Print Assumptions numerical_seed_executes_realized.
