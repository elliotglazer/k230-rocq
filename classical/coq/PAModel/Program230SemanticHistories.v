(** Actual semantic p230 histories inherit the checked arithmetic history constructors. *)
From PAModel Require Import Model Arithmetic FiniteCoding Program230Configurations Program230Histories
 Program230HistoryJoin Program230HistoryConstructors Program230TransferProgram Program230InstructionFormula.
From K230 Require Import Prog230.
Unset Implicit Arguments.
Lemma p230_program_history_zero M start:exists b c,
 program230_program_history M p230 b c(zeroM M)start /\program230_state_at M b c(zeroM M)start.
Proof.
 destruct(program230_history_zero M p230_instruction_formula start)as[b[c[HR HT]]].
 exists b,c;split;[apply p230_instruction_history_correct;exact HR|exact HT].
Qed.
Lemma p230_program_history_one M start final:
 Program230Histories.program230_step M p230_instruction_formula start final->exists b c,
 program230_program_history M p230 b c(succM M(zeroM M))start /\
 program230_state_at M b c(succM M(zeroM M))final.
Proof.
 intro HS;destruct(program230_history_one M p230_instruction_formula start final HS)as[b[c[HR HT]]].
 exists b,c;split;[apply p230_instruction_history_correct;exact HR|exact HT].
Qed.
Theorem p230_program_history_join M b c N d e K start middle:
 program230_program_history M p230 b c N start->program230_state_at M b c N middle->
 program230_program_history M p230 d e K middle->
 exists f g,program230_program_history M p230 f g(addM M N K)start /\
 (forall i s,coding_lt M i(succM M N)->(program230_state_at M b c i s<->program230_state_at M f g i s)) /\
 (forall i s,coding_lt M i(succM M K)->(program230_state_at M d e i s<->program230_state_at M f g(addM M N i)s)).
Proof.
 intros HN HM HK;apply(proj2(p230_instruction_history_correct M b c N start))in HN.
 apply(proj2(p230_instruction_history_correct M d e K middle))in HK.
 destruct(program230_history_join M p230_instruction_formula b c N d e K start middle HN HM HK)as[f[g[HR HX]]].
 exists f,g;split;[apply p230_instruction_history_correct;exact HR|exact HX].
Qed.
Theorem p230_program_history_extend M b c N start middle final:
 program230_program_history M p230 b c N start->program230_state_at M b c N middle->
 Program230Histories.program230_step M p230_instruction_formula middle final->
 exists d e,program230_program_history M p230 d e(succM M N)start /\
 program230_state_at M d e(succM M N)final.
Proof.
 intros HR HM HS;apply(proj2(p230_instruction_history_correct M b c N start))in HR.
 destruct(program230_history_extend M p230_instruction_formula b c N start middle final HR HM HS)
 as[d[e[HP[HT _]]]]. exists d,e;split;[apply p230_instruction_history_correct;exact HP|exact HT].
Qed.
Print Assumptions p230_program_history_join.
Print Assumptions p230_program_history_extend.
