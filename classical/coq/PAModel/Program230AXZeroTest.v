(** Actual equality-gated clearing of the top register. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
 Program230Configurations Program230Histories Program230HistoryJoin Program230InstructionFormula
 Program230PathCode Program230TransferStates Program230TransferProgram Program230ResetLoop
 Program230ComparisonIteration Program230EqualitySites Program230TopReset Program230UnpairRestore.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition p230_ax_test_state{D}(base:program230_configuration D)pc top x y:=
 program230_comparison_state(p230_top_state base pc top)pc x y.
Theorem p230_ax_zero_test M P n base top x y out:
 p230_equality_site P ->program230_reset_occurrence p230(inc_path P)1 n ->
 ((x=y /\out=zeroM M)\/(x<>y /\out=top)) ->
 exists b c time Q,program230_history M p230_instruction_formula b c time
  (p230_ax_test_state base(program230_path_value M P)top x y) /\
 program230_state_at M b c time(p230_ax_test_state base(program230_path_value M Q)out(zeroM M)(zeroM M)) /\
 coding_lt M(zeroM M)time /\
 ((x=y /\Q=inc_path(inc_path P))\/(x<>y /\Q=brk 1 P)).
Proof.
 intros HS HR [[Hxy ->]|[Hxy ->]].
 -destruct(proj1(p230_equality_site_histories M P(p230_top_state base(program230_path_value M P)top)x y HS)Hxy)
  as[b[c[N[HB[HC HN]]]]].
  set(clear:=program230_comparison_state base(program230_path_value M(inc_path P))(zeroM M)(zeroM M)).
  destruct(p230_top_reset_padded M(inc_path P)n clear top HR)as[d[e[HD HE]]].
  change(program230_history M p230_instruction_formula d e(program230_reset_time M top)
    (p230_ax_test_state base(program230_path_value M(inc_path P++[false]))top(zeroM M)(zeroM M)))in HD.
  change(program230_state_at M d e(program230_reset_time M top)
    (p230_ax_test_state base(program230_path_value M(inc_path(inc_path P)))(zeroM M)(zeroM M)(zeroM M)))in HE.
  destruct(program230_history_join M p230_instruction_formula b c N d e(program230_reset_time M top)
   _ _ HB HC HD)as[f[g[HF[HL Hright]]]].
  exists f,g,(addM M N(program230_reset_time M top)),(inc_path(inc_path P));split;[exact HF|].
  split;[exact(proj1(Hright _ _(coding_lt_succ M _))HE)|].
  split;[apply program230_positive_sum;exact HN|left;auto].
 -destruct(proj2(p230_equality_site_histories M P(p230_top_state base(program230_path_value M P)top)x y HS)Hxy)
  as[b[c[N[HB[HC HN]]]]].
  exists b,c,N,(brk 1 P);split;[exact HB|]. split;[exact HC|]. split;[exact HN|right;auto].
Qed.
Print Assumptions p230_ax_zero_test.
