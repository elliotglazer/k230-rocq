(** Equality gates retain the physical padded source PC. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
 Program230Configurations Program230Histories Program230InstructionFormula Program230PathCode
 Program230RootHistory Program230AXZeroTest Program230EqualitySites Program230ResetLoop.
From K230 Require Import RM RMEquiv Prog230.
Unset Implicit Arguments.
Lemma p230_ax_zero_test_padded M P Q n base top x y out:
 p230_equality_site P ->program230_reset_occurrence p230(inc_path P)1 n ->ipeq Q P ->
 ((x=y /\out=zeroM M)\/(x<>y /\out=top)) ->
 exists b c time R,program230_history M p230_instruction_formula b c time
  (p230_ax_test_state base(program230_path_value M Q)top x y) /\
 program230_state_at M b c time(p230_ax_test_state base(program230_path_value M R)out(zeroM M)(zeroM M)) /\
 coding_lt M(zeroM M)time /\
 ((x=y /\R=inc_path(inc_path P))\/(x<>y /\R=brk 1 P)).
Proof.
 intros HS HR HQ HO.
 destruct(p230_ax_zero_test M P n base top x y out HS HR HO)as[b[c[N[R[HB[HC[HN HE]]]]]]].
 assert(Hnz:N<>zeroM M)by(intro E;rewrite E in HN;destruct HN as[t Ht];rewrite coding_add_zero in Ht;exact(zero_ne_succ M t Ht)).
 destruct(p230_history_ipeq_endpoint M b c N
  (p230_ax_test_state base(program230_path_value M P)top x y)P Q
  (p230_ax_test_state base(program230_path_value M R)out(zeroM M)(zeroM M))
  eq_refl(ipeq_sym Q P HQ)HB Hnz HC)as[d[e[HD[HF _]]]].
 exists d,e,N,R;exact(conj HD(conj HF(conj HN HE))).
Qed.
Print Assumptions p230_ax_zero_test_padded.
