(** Literal post-action returns. These start after the action has completed. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
 Program230Configurations Program230Histories Program230HistoryConstructors
 Program230InstructionFormula Program230RootReady Program230RootHistory
 Program230Selector Program230RotatedRestore Program230PathCode Program230Edges.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.
Section Returns.
Variable M:Model.
Local Notation N:=(code_numeral M).
Local Notation cfg:=program230_with_pc.
Lemma p230_selector_break_0 base:
 Program230Histories.program230_step M p230_instruction_formula
 (cfg base(program230_path_value M p230_selector_return_0))
 (cfg base(program230_path_value M p230_selector_return_exit)).
Proof.
 eapply(p230_rotated_literal M p230_selector_return_0 p230_selector_return_0(EBreak 1));[reflexivity|apply p230_rotated_read|reflexivity|reflexivity|].
 cbn[program230_edge_step];split;[reflexivity|]. intros i Hi;now rewrite !program230_with_pc_register.
Qed.
Lemma p230_selector_break_1 base:
 Program230Histories.program230_step M p230_instruction_formula
 (cfg base(program230_path_value M p230_selector_return_1))
 (cfg base(program230_path_value M p230_selector_return_0)).
Proof.
 eapply(p230_rotated_literal M p230_selector_return_1 p230_selector_return_1(EBreak 1));[reflexivity|apply p230_rotated_read|reflexivity|reflexivity|].
 cbn[program230_edge_step];split;[reflexivity|]. intros i Hi;now rewrite !program230_with_pc_register.
Qed.
Lemma p230_selector_break_2 base:
 Program230Histories.program230_step M p230_instruction_formula
 (cfg base(program230_path_value M p230_selector_return_2))
 (cfg base(program230_path_value M p230_selector_return_1)).
Proof.
 eapply(p230_rotated_literal M p230_selector_return_2 p230_selector_return_2(EBreak 1));[reflexivity|apply p230_rotated_read|reflexivity|reflexivity|].
 cbn[program230_edge_step];split;[reflexivity|]. intros i Hi;now rewrite !program230_with_pc_register.
Qed.
Lemma p230_selector_one_return base:
 exists b c,program230_history M p230_instruction_formula b c(N 1)
 (cfg base(program230_path_value M p230_selector_return_0)) /\
 program230_state_at M b c(N 1)(cfg base(program230_path_value M p230_selector_return_exit)).
Proof. apply program230_history_one;apply p230_selector_break_0. Qed.
Lemma p230_selector_two_return base:
 exists b c,program230_history M p230_instruction_formula b c(N 2)
 (cfg base(program230_path_value M p230_selector_return_1)) /\
 program230_state_at M b c(N 2)(cfg base(program230_path_value M p230_selector_return_exit)).
Proof.
 destruct(program230_history_one M p230_instruction_formula _ _(p230_selector_break_1 base))as[b[c[HR HT]]].
 destruct(program230_history_extend M p230_instruction_formula b c(N 1)_ _ _ HR HT(p230_selector_break_0 base))as[d[e[HD[HE _]]]].
 exists d,e;exact(conj HD HE).
Qed.
Theorem p230_selector_ax_return base:
 exists b c,program230_history M p230_instruction_formula b c(N 3)
 (cfg base(program230_path_value M(inc_path p230_selector_ax))) /\
 program230_state_at M b c(N 3)(cfg base(program230_path_value M p230_selector_return_exit)).
Proof.
 destruct(program230_history_one M p230_instruction_formula _ _(p230_selector_break_2 base))as[b[c[HR HT]]].
 destruct(program230_history_extend M p230_instruction_formula b c(N 1)_ _ _ HR HT(p230_selector_break_1 base))as[d[e[HD[HE _]]]].
 destruct(program230_history_extend M p230_instruction_formula d e(N 2)_ _ _ HD HE(p230_selector_break_0 base))as[f[g[HF[HG _]]]].
 exists f,g;exact(conj HF HG).
Qed.
Theorem p230_selector_drop_return base:
 exists b c,program230_history M p230_instruction_formula b c(N 1)
 (cfg base(program230_path_value M(inc_path p230_selector_drop))) /\
 program230_state_at M b c(N 1)(cfg base(program230_path_value M p230_selector_return_exit)).
Proof.
 destruct(p230_selector_one_return base)as[b[c[HR HT]]].
 assert(Hip:ipeq p230_selector_return_0(inc_path p230_selector_drop)).
 {apply ipeq_sym;exact(ipeq_app_false p230_selector_return_0). }
 assert(Hnz:N 1<>zeroM M)by(intro E;exact(zero_ne_succ M(zeroM M)(eq_sym E))).
 destruct(p230_history_ipeq_endpoint M b c(N 1)
  (cfg base(program230_path_value M p230_selector_return_0))p230_selector_return_0
  (inc_path p230_selector_drop)(cfg base(program230_path_value M p230_selector_return_exit))
  eq_refl Hip HR Hnz HT)as[d[e[HD[HE _]]]].
 exists d,e;exact(conj HD HE).
Qed.
Theorem p230_selector_nip_return base:
 exists b c,program230_history M p230_instruction_formula b c(N 2)
 (cfg base(program230_path_value M(inc_path p230_selector_nip))) /\
 program230_state_at M b c(N 2)(cfg base(program230_path_value M p230_selector_return_exit)).
Proof.
 destruct(p230_selector_two_return base)as[b[c[HR HT]]].
 assert(Hip:ipeq p230_selector_return_1(inc_path p230_selector_nip)).
 {apply ipeq_sym;exact(ipeq_app_false p230_selector_return_1). }
 assert(Hnz:N 2<>zeroM M)by(intro E;exact(zero_ne_succ M(N 1)(eq_sym E))).
 destruct(p230_history_ipeq_endpoint M b c(N 2)
  (cfg base(program230_path_value M p230_selector_return_1))p230_selector_return_1
  (inc_path p230_selector_nip)(cfg base(program230_path_value M p230_selector_return_exit))
  eq_refl Hip HR Hnz HT)as[d[e[HD[HE _]]]].
 exists d,e;exact(conj HD HE).
Qed.
Lemma p230_selector_return_ready:
 program230_root_ready M(program230_path_value M p230_selector_return_exit).
Proof. apply program230_root_ready_of_zero_path;[cbn;lia|change(ipeq(repeat false 3)(@nil bool));apply program230_repeat_false_ipeq]. Qed.
Lemma p230_selector_mp_return_ready:
 program230_root_ready M(program230_path_value M(inc_path p230_selector_mp)).
Proof. apply program230_root_ready_of_zero_path;[cbn;lia|change(ipeq(repeat false 4)(@nil bool));apply program230_repeat_false_ipeq]. Qed.
End Returns.
Print Assumptions p230_selector_drop_return.
Print Assumptions p230_selector_nip_return.
Print Assumptions p230_selector_ax_return.
Print Assumptions p230_selector_return_ready.
