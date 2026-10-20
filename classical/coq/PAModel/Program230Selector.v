(** Finite action dispatch in the literal p230 tree, after selector decoding. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
 Program230Configurations Program230Histories Program230HistoryConstructors
 Program230InstructionFormula Program230RootReady Program230RootHistory
 Program230TransferStates Program230RotatedRestore Program230PathCode Program230Read Program230PathPop Program230Walk Program230Edges.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Bool.Bool Lia.
Import ListNotations.
Unset Implicit Arguments.
Definition p230_selector_path:list bool := [true;true;true].
Definition p230_selector_second:list bool := [true;true;true;false;true].
Definition p230_selector_third:list bool := [true;true;true;false;true;false;false;true].
Definition p230_selector_mp:list bool := [true;true;true;true].
Definition p230_selector_drop:list bool := [true;true;true;false;true;false;true].
Definition p230_selector_nip:list bool := [true;true;true;false;true;false;false;true;false;true].
Definition p230_selector_ax_short:list bool := [true;true;true;false;true;false;false;true;false;false;true].
Definition p230_selector_ax:list bool := [true;true;true;false;true;false;false;true;false;false;true;false].
Definition p230_selector_return_0:list bool := [true;true;true;false;true;true].
Definition p230_selector_return_1:list bool := [true;true;true;false;true;false;false;true;true].
Definition p230_selector_return_2:list bool := [true;true;true;false;true;false;false;true;false;false;true;true].
Definition p230_selector_return_exit:list bool := [false;false;false].
Definition p230_selector_cfg {D}(base:program230_configuration D)pc selector:=
 program230_transfer_state 3 3 base pc selector selector.
Lemma p230_selector_read_zeros M n:
 program230_read M(code_numeral M 1)(repeat false n)(code_numeral M 1).
Proof.
 induction n as[|n IH];[reflexivity|];cbn[repeat program230_read].
 exists(code_numeral M 1);split;[left;repeat split;reflexivity|exact IH].
Qed.
Lemma p230_selector_read_padding M P n:
 program230_read M(program230_path_value M P)(P++repeat false n)(code_numeral M 1).
Proof. apply program230_read_app;exists(code_numeral M 1);split;[apply p230_rotated_read|apply p230_selector_read_zeros]. Qed.
Section Prefix.
Variable M:Model.
Local Notation Z:=(zeroM M).
Local Notation S:=(succM M).
Local Notation N:=(code_numeral M).
Local Notation cfg:=p230_selector_cfg.
Lemma p230_selector_first_zero base:
 Program230Histories.program230_step M p230_instruction_formula
 (cfg base(program230_path_value M p230_selector_path)Z)
 (cfg base(program230_path_value M p230_selector_mp)Z).
Proof.
 eapply(p230_rotated_literal M p230_selector_path(p230_selector_path++repeat false 2)(EDecnz 3));[reflexivity|apply p230_selector_read_padding|reflexivity|reflexivity|].
 cbn[program230_edge_step];split;[lia|];left;split.
 -unfold p230_selector_cfg;rewrite program230_transfer_register by lia;reflexivity.
 -split;[reflexivity|]. intros i Hi;unfold p230_selector_cfg;rewrite !program230_transfer_register by exact Hi.
  do 9(destruct i as[|i];[reflexivity|]);lia.
Qed.
Lemma p230_selector_first_positive base c:
 Program230Histories.program230_step M p230_instruction_formula
 (cfg base(program230_path_value M p230_selector_path)(S c))
 (cfg base(program230_path_value M p230_selector_second)c).
Proof.
 eapply(p230_rotated_literal M p230_selector_path(p230_selector_path++repeat false 2)(EDecnz 3));[reflexivity|apply p230_selector_read_padding|reflexivity|reflexivity|].
 cbn[program230_edge_step];split;[lia|];right;exists c;split.
 -unfold p230_selector_cfg;rewrite program230_transfer_register by lia;reflexivity.
 -split;[reflexivity|]. intros i Hi;unfold p230_selector_cfg;rewrite !program230_transfer_register by exact Hi.
  do 9(destruct i as[|i];[reflexivity|]);lia.
Qed.
Lemma p230_selector_second_zero base:
 Program230Histories.program230_step M p230_instruction_formula
 (cfg base(program230_path_value M p230_selector_second)Z)
 (cfg base(program230_path_value M p230_selector_drop)Z).
Proof.
 eapply(p230_rotated_literal M p230_selector_second(p230_selector_second++repeat false 3)(EDecnz 3));[reflexivity|apply p230_selector_read_padding|reflexivity|reflexivity|].
 cbn[program230_edge_step];split;[lia|];left;split.
 -unfold p230_selector_cfg;rewrite program230_transfer_register by lia;reflexivity.
 -split;[reflexivity|]. intros i Hi;unfold p230_selector_cfg;rewrite !program230_transfer_register by exact Hi.
  do 9(destruct i as[|i];[reflexivity|]);lia.
Qed.
Lemma p230_selector_second_positive base c:
 Program230Histories.program230_step M p230_instruction_formula
 (cfg base(program230_path_value M p230_selector_second)(S c))
 (cfg base(program230_path_value M p230_selector_third)c).
Proof.
 eapply(p230_rotated_literal M p230_selector_second(p230_selector_second++repeat false 3)(EDecnz 3));[reflexivity|apply p230_selector_read_padding|reflexivity|reflexivity|].
 cbn[program230_edge_step];split;[lia|];right;exists c;split.
 -unfold p230_selector_cfg;rewrite program230_transfer_register by lia;reflexivity.
 -split;[reflexivity|]. intros i Hi;unfold p230_selector_cfg;rewrite !program230_transfer_register by exact Hi.
  do 9(destruct i as[|i];[reflexivity|]);lia.
Qed.
Lemma p230_selector_third_zero base:
 Program230Histories.program230_step M p230_instruction_formula
 (cfg base(program230_path_value M p230_selector_third)Z)
 (cfg base(program230_path_value M p230_selector_nip)Z).
Proof.
 eapply(p230_rotated_literal M p230_selector_third(p230_selector_third++repeat false 3)(EDecnz 3));[reflexivity|apply p230_selector_read_padding|reflexivity|reflexivity|].
 cbn[program230_edge_step];split;[lia|];left;split.
 -unfold p230_selector_cfg;rewrite program230_transfer_register by lia;reflexivity.
 -split;[reflexivity|]. intros i Hi;unfold p230_selector_cfg;rewrite !program230_transfer_register by exact Hi.
  do 9(destruct i as[|i];[reflexivity|]);lia.
Qed.
Lemma p230_selector_third_positive base c:
 Program230Histories.program230_step M p230_instruction_formula
 (cfg base(program230_path_value M p230_selector_third)(S c))
 (cfg base(program230_path_value M p230_selector_ax_short)c).
Proof.
 eapply(p230_rotated_literal M p230_selector_third(p230_selector_third++repeat false 3)(EDecnz 3));[reflexivity|apply p230_selector_read_padding|reflexivity|reflexivity|].
 cbn[program230_edge_step];split;[lia|];right;exists c;split.
 -unfold p230_selector_cfg;rewrite program230_transfer_register by lia;reflexivity.
 -split;[reflexivity|]. intros i Hi;unfold p230_selector_cfg;rewrite !program230_transfer_register by exact Hi.
  do 9(destruct i as[|i];[reflexivity|]);lia.
Qed.
Theorem p230_selector_dispatch_mp base:
 exists b c,program230_history M p230_instruction_formula b c(N 1)
 (cfg base(program230_path_value M p230_selector_path)Z) /\
 program230_state_at M b c(N 1)(cfg base(program230_path_value M p230_selector_mp)Z).
Proof. apply program230_history_one;apply p230_selector_first_zero. Qed.
Theorem p230_selector_dispatch_drop base:
 exists b c,program230_history M p230_instruction_formula b c(N 2)
 (cfg base(program230_path_value M p230_selector_path)(N 1)) /\
 program230_state_at M b c(N 2)(cfg base(program230_path_value M p230_selector_drop)Z).
Proof.
 destruct(program230_history_one M p230_instruction_formula _ _(p230_selector_first_positive base Z))as[b[c[HR HT]]].
 destruct(program230_history_extend M p230_instruction_formula b c(N 1)_ _ _ HR HT(p230_selector_second_zero base))as[d[e[HD[HE _]]]].
 exists d,e;exact(conj HD HE).
Qed.
Theorem p230_selector_dispatch_nip base:
 exists b c,program230_history M p230_instruction_formula b c(N 3)
 (cfg base(program230_path_value M p230_selector_path)(N 2)) /\
 program230_state_at M b c(N 3)(cfg base(program230_path_value M p230_selector_nip)Z).
Proof.
 destruct(program230_history_one M p230_instruction_formula _ _(p230_selector_first_positive base(N 1)))as[b[c[HR HT]]].
 destruct(program230_history_extend M p230_instruction_formula b c(N 1)_ _ _ HR HT(p230_selector_second_positive base Z))as[d[e[HD[HE _]]]].
 destruct(program230_history_extend M p230_instruction_formula d e(N 2)_ _ _ HD HE(p230_selector_third_zero base))as[f[g[HF[HG _]]]].
 exists f,g;exact(conj HF HG).
Qed.
Theorem p230_selector_dispatch_ax base selector:
 exists b c,program230_history M p230_instruction_formula b c(N 3)
 (cfg base(program230_path_value M p230_selector_path)(S(S(S selector)))) /\
 program230_state_at M b c(N 3)(cfg base(program230_path_value M p230_selector_ax_short)selector).
Proof.
 destruct(program230_history_one M p230_instruction_formula _ _(p230_selector_first_positive base(S(S selector))))as[b[c[HR HT]]].
 destruct(program230_history_extend M p230_instruction_formula b c(N 1)_ _ _ HR HT(p230_selector_second_positive base(S selector)))as[d[e[HD[HE _]]]].
 destruct(program230_history_extend M p230_instruction_formula d e(N 2)_ _ _ HD HE(p230_selector_third_positive base selector))as[f[g[HF[HG _]]]].
 exists f,g;exact(conj HF HG).
Qed.
End Prefix.
Lemma p230_selector_ax_entry_ipeq:ipeq p230_selector_ax_short p230_selector_ax.
Proof. apply ipeq_sym;exact(ipeq_app_false p230_selector_ax_short). Qed.
Lemma p230_selector_mp_actual:fol p230(ENode(root p230))p230_selector_mp=Some(ENode 5032).
Proof. reflexivity. Qed.
Lemma p230_selector_drop_actual:fol p230(ENode(root p230))p230_selector_drop=Some(ENode 5007).
Proof. reflexivity. Qed.
Lemma p230_selector_nip_actual:fol p230(ENode(root p230))p230_selector_nip=Some(ENode 4981).
Proof. reflexivity. Qed.
Lemma p230_selector_ax_actual:fol p230(ENode(root p230))p230_selector_ax=Some(ENode 46).
Proof. reflexivity. Qed.
Print Assumptions p230_selector_dispatch_mp.
Print Assumptions p230_selector_dispatch_drop.
Print Assumptions p230_selector_dispatch_nip.
Print Assumptions p230_selector_dispatch_ax.
