(** Actual candidate fetch from the initial p230 root, including rotated restore. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
 Program230Configurations Program230Histories Program230HistoryJoin Program230HistoryConstructors
 Program230InstructionFormula Program230RootReady Program230RootHistory
 Program230TransferStates Program230TransferProgram Program230Copy2States Program230Copy2Loop
 Program230Copy2Program Program230RotatedRestore Program230PathCode Program230Read Program230Edges.
From FOL Require Import FullSyntax Arithmetics.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Bool.Bool Lia setoid_ring.Ring.
Import ListNotations.
Unset Implicit Arguments.
(** Internally used normal form fixes scratch6 at zero. *)
Definition p230_fetch_cfg M base pc candidate program:=
 program230_copy2_state 0 8 6 base pc candidate program (zeroM M).
Definition p230_fetch_time M n:=addM M(mulM M(code_numeral M 7)n)(code_numeral M 4).
Lemma p230_fetch_copy_occurrence:
 program230_copy2_occurrence p230 ([false;true;false]) 0 8 6 4 5 6.
Proof. unfold program230_copy2_occurrence;repeat split;reflexivity. Qed.
Lemma p230_fetch_read_initial M:
 program230_read M(code_numeral M 1)([false;false;false])(code_numeral M 1).
Proof. pose proof(program230_read_path M 3 (@nil bool))as H;exact H. Qed.
Section Fetch.
Variable M:Model.
Local Notation Z:=(zeroM M).
Local Notation S:=(succM M).
Local Notation N:=(code_numeral M).
Local Notation cfg:=(p230_fetch_cfg M).
Add Ring candidate_fetch_ring:(model_semiring M).
Lemma p230_fetch_numeral_sum a b:
 addM M(N a)(N b)=N(a+b).
Proof. induction a as[|a IH].
 -exact(Arithmetic.add_zero M(N b)).
 -change(addM M(S(N a))(N b)=S(N(a+b)));rewrite(Arithmetic.add_succ M(N a)(N b)),IH;reflexivity. Qed.
Lemma p230_fetch_dec_zero base n:
 Program230Histories.program230_step M p230_instruction_formula
 (cfg base(N 1)n Z)
 (cfg base(program230_path_value M([false;true]))n Z).
Proof.
 eapply(p230_rotated_literal M(@nil bool)([false;false;false])(EDecnz 8));[reflexivity|apply p230_fetch_read_initial|reflexivity|reflexivity|].
 cbn[program230_edge_step];split;[lia|];left;split.
 -unfold p230_fetch_cfg;rewrite program230_copy2_register by lia;reflexivity.
 -split;[reflexivity|]. intros i Hi;unfold p230_fetch_cfg;rewrite !program230_copy2_register by exact Hi;reflexivity.
Qed.
Lemma p230_fetch_dec_positive base n q:
 Program230Histories.program230_step M p230_instruction_formula
 (cfg base(N 1)n(S q))
 (cfg base(program230_path_value M([false;false;true]))n q).
Proof.
 eapply(p230_rotated_literal M(@nil bool)([false;false;false])(EDecnz 8));[reflexivity|apply p230_fetch_read_initial|reflexivity|reflexivity|].
 cbn[program230_edge_step];split;[lia|];right;exists q;split.
 -unfold p230_fetch_cfg;rewrite program230_copy2_register by lia;reflexivity.
 -split;[reflexivity|]. intros i Hi;unfold p230_fetch_cfg;rewrite !program230_copy2_register by exact Hi.
  do 9(destruct i as[|i];[reflexivity|]);lia.
Qed.
Lemma p230_fetch_skip base n q:
 Program230Histories.program230_step M p230_instruction_formula
 (cfg base(program230_path_value M([false;false;true]))n q)
 (cfg base(program230_path_value M([true]))n q).
Proof.
 eapply(p230_rotated_literal M([false;false;true])([false;false;true])(EBreak 1));[reflexivity|apply p230_rotated_read|reflexivity|reflexivity|].
 cbn[program230_edge_step];split;[reflexivity|]. intros i Hi;unfold p230_fetch_cfg;rewrite !program230_copy2_register by exact Hi;reflexivity.
Qed.
Theorem p230_candidate_fetch_positive base n q:
 exists b c,program230_history M p230_instruction_formula b c(N 2)(cfg base(N 1)n(S q)) /\
 program230_state_at M b c(N 2)(cfg base(program230_path_value M([true]))n q).
Proof.
 destruct(program230_history_one M p230_instruction_formula _ _(p230_fetch_dec_positive base n q))as[b[c[HR HT]]].
 destruct(program230_history_extend M p230_instruction_formula b c(N 1)_ _ _ HR HT(p230_fetch_skip base n q))as[d[e[HR' [HT' _]]]].
 exists d,e;exact(conj HR' HT').
Qed.
Lemma p230_fetch_copy base n:
 exists b c,program230_history M p230_instruction_formula b c(program230_copy2_time M n)
 (cfg base(program230_path_value M([false;true;false]))n Z) /\
 program230_state_at M b c(program230_copy2_time M n)
 (program230_copy2_state 0 8 6 base(program230_path_value M p230_rotated_path)Z n n).
Proof.
 destruct(program230_copy2_program_history M p230([false;true;false])0 8 6 4 5 6
  (cfg base(program230_path_value M([false;true;false]))n Z)n
  ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)
  p230_fetch_copy_occurrence eq_refl ltac:(unfold p230_fetch_cfg;rewrite program230_copy2_register by lia;reflexivity))
  as[b[c[last[HR[HT[HP[H0[H8[H6 Hrest]]]]]]]]].
 assert(H8':program230_register last 8=n).
 {rewrite H8;unfold p230_fetch_cfg;rewrite program230_copy2_register by lia;apply coding_add_zero. }
 assert(H6':program230_register last 6=n).
 {rewrite H6;unfold p230_fetch_cfg;rewrite program230_copy2_register by lia;apply coding_add_zero. }
 assert(Hlast:last=program230_copy2_state 0 8 6 base(program230_path_value M p230_rotated_path)Z n n).
 {apply p230_configuration_ext;intros j Hj;destruct j as[|j];[exact HP|].
  change(program230_register last j=program230_register(program230_copy2_state 0 8 6 base(program230_path_value M p230_rotated_path)Z n n)j).
  rewrite program230_copy2_register by lia.
  destruct(Nat.eqb j 0)eqn:E0;[apply Nat.eqb_eq in E0;subst j;exact H0|].
  destruct(Nat.eqb j 8)eqn:E8;[apply Nat.eqb_eq in E8;subst j;exact H8'|].
  destruct(Nat.eqb j 6)eqn:E6;[apply Nat.eqb_eq in E6;subst j;exact H6'|].
  rewrite Hrest by(apply Nat.eqb_neq in E0,E8,E6;lia).
  unfold p230_fetch_cfg;rewrite program230_copy2_register by lia;now rewrite E0,E8,E6. }
 subst last;exists b,c;split;[apply(proj2(p230_instruction_history_correct M b c(program230_copy2_time M n)_));exact HR|exact HT].
Qed.
Lemma p230_fetch_copy_open base n:
 exists b c,program230_history M p230_instruction_formula b c(program230_copy2_time M n)
 (cfg base(program230_path_value M([false;true]))n Z) /\
 program230_state_at M b c(program230_copy2_time M n)
 (program230_copy2_state 0 8 6 base(program230_path_value M p230_rotated_path)Z n n).
Proof.
 destruct(p230_fetch_copy base n)as[b[c[HR HT]]].
 assert(Hnz:program230_copy2_time M n<>Z).
 {unfold program230_copy2_time;change(addM M(mulM M(N 4)n)(S Z)<>Z).
  rewrite <-(succ_as_add M(mulM M(N 4)n));intro E;apply(zero_ne_succ M(mulM M(N 4)n));symmetry;exact E. }
 destruct(p230_history_ipeq_endpoint M b c(program230_copy2_time M n)
  (cfg base(program230_path_value M([false;true;false]))n Z)
  ([false;true;false])([false;true])
  (program230_copy2_state 0 8 6 base(program230_path_value M p230_rotated_path)Z n n)
  eq_refl (ipeq_app_false ([false;true]))HR Hnz HT)as[d[e[HD[HE _]]]].
 assert(HS:program230_with_pc(cfg base(program230_path_value M([false;true;false]))n Z)
   (program230_path_value M([false;true]))=cfg base(program230_path_value M([false;true]))n Z).
 {apply p230_configuration_ext;intros j Hj;do 10(destruct j;[reflexivity|]);lia. }
 rewrite HS in HD;exists d,e;exact(conj HD HE).
Qed.
Theorem p230_candidate_fetch_zero base n:
 exists b c,program230_history M p230_instruction_formula b c(p230_fetch_time M n)(cfg base(N 1)n Z) /\
 program230_state_at M b c(p230_fetch_time M n)
 (cfg base(program230_path_value M p230_rotated_exit)(S n)n).
Proof.
 destruct(p230_fetch_copy_open base n)as[b[c[HC HTC]]].
 destruct(p230_rotated_restore_uniform M
  (program230_copy2_state 0 8 6 base(program230_path_value M p230_rotated_path)Z n n)n Z)
  as[d[e[HR HTR]]].
 assert(HS:p230_rotated_state(program230_copy2_state 0 8 6 base(program230_path_value M p230_rotated_path)Z n n)
  (program230_path_value M p230_rotated_path)n Z=
  program230_copy2_state 0 8 6 base(program230_path_value M p230_rotated_path)Z n n).
 {unfold p230_rotated_state;apply program230_transfer_state_restore;[reflexivity| |];rewrite program230_copy2_register by lia;reflexivity. }
 rewrite HS in HR.
 assert(HE:p230_rotated_state(program230_copy2_state 0 8 6 base(program230_path_value M p230_rotated_path)Z n n)
  (program230_path_value M p230_rotated_exit)Z(addM M(addM M Z n)(N 1))=
  cfg base(program230_path_value M p230_rotated_exit)(S n)n).
 {assert(E:addM M(addM M Z n)(N 1)=S n)by(rewrite coding_add_zero;symmetry;apply succ_as_add).
  rewrite E;apply p230_configuration_ext;intros j Hj.
  do 10(destruct j;[reflexivity|]);lia. }
 rewrite HE in HTR.
 destruct(program230_history_join M p230_instruction_formula b c(program230_copy2_time M n)
  d e(p230_rotated_time M n)_ _ HC HTC HR)as[f[g[HJ[HL HJlast]]]].
 assert(HTsum:addM M(program230_copy2_time M n)(p230_rotated_time M n)=addM M(mulM M(N 7)n)(N 3)).
 {assert(E7:N 7=addM M(N 4)(N 3))by(exact(eq_sym(p230_fetch_numeral_sum 4 3))).
  assert(E3:N 3=addM M(N 1)(N 2))by(exact(eq_sym(p230_fetch_numeral_sum 1 2))).
  unfold program230_copy2_time,p230_rotated_time;rewrite E7,E3;ring. }
 assert(HF:program230_state_at M f g(addM M(mulM M(N 7)n)(N 3))(cfg base(program230_path_value M p230_rotated_exit)(S n)n)).
 {rewrite <-HTsum;apply(HJlast(p230_rotated_time M n)_ (coding_lt_succ M(p230_rotated_time M n)));exact HTR. }
 rewrite HTsum in HJ.
 destruct(program230_history_one M p230_instruction_formula _ _(p230_fetch_dec_zero base n))as[u[v[H0 HT0]]].
 destruct(program230_history_join M p230_instruction_formula u v(N 1)f g(addM M(mulM M(N 7)n)(N 3))_ _ H0 HT0 HJ)
  as[r[s[HRun[_ HLast]]]].
 assert(ET:addM M(N 1)(addM M(mulM M(N 7)n)(N 3))=p230_fetch_time M n)by(assert(E4:N 4=addM M(N 1)(N 3))by(exact(eq_sym(p230_fetch_numeral_sum 1 3)));unfold p230_fetch_time;rewrite E4;ring).
 exists r,s;split;[now rewrite <-ET|].
 rewrite <-ET;apply(HLast(addM M(mulM M(N 7)n)(N 3))_ (coding_lt_succ M(addM M(mulM M(N 7)n)(N 3))));exact HF.
Qed.
End Fetch.
Print Assumptions p230_candidate_fetch_positive.
Print Assumptions p230_candidate_fetch_zero.
