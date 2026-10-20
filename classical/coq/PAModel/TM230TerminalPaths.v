(** A genuine terminal-state path cannot have a longer path from its start.
    Both lengths may be nonstandard model elements. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions
 TM230LiteralActions TM230TransitionArithmetic TM230TableBounds TM230BinaryStep
 TM230RunArithmetic TM230RunComposition TM230StandardRun TM230StandardPacking
 TM230MacroProgress TM230PathDeterminism.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Theorem machine230_terminal_no_step M s t:
 machine230_state s=code_numeral M 230 ->~machine230_step M s t.
Proof.
 intros HS[w[d[[a[Hin HA]]Hrest]]].
 destruct a as[[[[q b]v]dir]next].
 destruct HA as[HQ _].
 assert(E:q=230)by(apply(machine230_numeral_injective M q 230);congruence).
 pose proof(machine230_transition_bounds q b v dir next
  (proj1(machine230_action_exact q b v dir next)Hin))as[Hq _]. lia.
Qed.
Theorem machine230_terminal_path_maximal M b c N d e K start halted ending:
 machine230_path M b c N start halted ->machine230_state halted=code_numeral M 230 ->
 machine230_path M d e K start ending ->~coding_lt M N K.
Proof.
 intros[HR HT]Hhalt[HK HE]Hless.
 destruct(machine230_state_at_total M d e N)as[mid HM].
 assert(E:halted=mid).
 {exact(machine230_run_prefix_unique M b c N d e K start HR HK N
  (coding_lt_succ M N)(coding_lt_trans M N K(succM M K)Hless(coding_lt_succ M K))halted mid HT HM). }
 subst mid.
 destruct(machine230_state_at_total M d e(succM M N))as[next Hnext].
 exact(machine230_terminal_no_step M halted next Hhalt(proj2 HK N halted next Hless HM Hnext)).
Qed.
Print Assumptions machine230_terminal_no_step.
Print Assumptions machine230_terminal_path_maximal.
