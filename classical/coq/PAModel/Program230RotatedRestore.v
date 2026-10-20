(** Literal rotated next-candidate restore loop: increment before testing. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
 Program230Configurations Program230Histories Program230HistoryJoin Program230HistoryConstructors
 Program230InstructionFormula Program230TransferStates Program230PathCode Program230PathPop Program230Read Program230Walk
 Program230Edges Program230Transition.
From FOL Require Import FullSyntax Arithmetics.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Bool.Bool Lia setoid_ring.Ring.
Import ListNotations.
Unset Implicit Arguments.
Definition p230_rotated_path:list bool := [false;true;true].
Definition p230_rotated_exit:list bool := [true;false;false;false].
Definition p230_rotated_time M n:=addM M(mulM M(code_numeral M 3)n)(code_numeral M 2).
Definition p230_rotated_state {D}:= @program230_transfer_state D 6 0.
Lemma p230_rotated_read M P:
 program230_read M(program230_path_value M P)P(succM M(zeroM M)).
Proof.
 pose proof(program230_read_path M(length P)P)as H.
 rewrite program230_take_zeros_firstn in H by lia.
 now rewrite firstn_all,skipn_all in H.
Qed.
Lemma p230_rotated_read_zero M P:
 program230_read M(program230_path_value M P)(P++[false])(succM M(zeroM M)).
Proof.
 apply program230_read_app;exists(succM M(zeroM M));split;[apply p230_rotated_read|].
 cbn[program230_read];exists(succM M(zeroM M));split;[|reflexivity].
 left;repeat split;reflexivity.
Qed.
Lemma p230_rotated_literal M P Q e s t:
 program230_pc s=program230_path_value M P ->
 program230_read M(program230_path_value M P)Q(succM M(zeroM M)) ->
 fol p230(ENode(root p230))Q=Some e ->is_node e=false ->
 program230_edge_step M Q e(program230_register s)(program230_register t)(program230_pc t) ->
 Program230Histories.program230_step M p230_instruction_formula s t.
Proof.
 intros HP HR HF HE Hstep;apply p230_instruction_formula_correct.
 exists e,Q,(succM M(zeroM M));split;[split;[now rewrite HP|split;assumption]|exact Hstep].
Qed.
Section FiniteSteps.
Variable M:Model.
Local Notation Z:=(zeroM M).
Local Notation S:=(succM M).
Local Notation N:=(code_numeral M).
Local Notation cfg:=(p230_rotated_state).
Local Notation P:=p230_rotated_path.
Lemma p230_rotated_inc base n y:
 Program230Histories.program230_step M p230_instruction_formula
 (cfg base(program230_path_value M P)n y)
 (cfg base(program230_path_value M(P++[true]))n(S y)).
Proof.
 eapply(p230_rotated_literal M P(P++[false])(EInc 0));[reflexivity|apply p230_rotated_read_zero|reflexivity|reflexivity|].
 cbn[program230_edge_step];split;[lia|];split.
 -unfold P,p230_rotated_path;reflexivity.
 -intros i Hi;unfold p230_rotated_state;rewrite program230_transfer_target by lia.
  rewrite !program230_transfer_register by exact Hi.
  do 9(destruct i as[|i];[reflexivity|]);lia.
Qed.
Lemma p230_rotated_dec_zero base y:
 Program230Histories.program230_step M p230_instruction_formula
 (cfg base(program230_path_value M(P++[true]))Z y)
 (cfg base(program230_path_value M p230_rotated_exit)Z y).
Proof.
 eapply(p230_rotated_literal M(P++[true])(P++[true;false])(EDecnz 6));[reflexivity| |reflexivity|reflexivity|].
 -replace(P++[true;false])with((P++[true])++[false])by(rewrite <-app_assoc;reflexivity).
  apply p230_rotated_read_zero.
 -cbn[program230_edge_step];split;[lia|];left;split.
  +unfold p230_rotated_state;apply program230_transfer_source;lia.
  +split;[reflexivity|].
   intros i Hi;unfold p230_rotated_state;rewrite !program230_transfer_register by exact Hi;reflexivity.
Qed.
Lemma p230_rotated_dec_positive base n y:
 Program230Histories.program230_step M p230_instruction_formula
 (cfg base(program230_path_value M(P++[true]))(S n)y)
 (cfg base(program230_path_value M(P++[true;true]))n y).
Proof.
 eapply(p230_rotated_literal M(P++[true])(P++[true;false])(EDecnz 6));[reflexivity| |reflexivity|reflexivity|].
 -replace(P++[true;false])with((P++[true])++[false])by(rewrite <-app_assoc;reflexivity).
  apply p230_rotated_read_zero.
 -cbn[program230_edge_step];split;[lia|];right;exists n;split.
  +unfold p230_rotated_state;apply program230_transfer_source;lia.
  +split;[reflexivity|].
   intros i Hi;unfold p230_rotated_state;rewrite !program230_transfer_register by exact Hi.
   do 9(destruct i as[|i];[reflexivity|]);lia.
Qed.
Lemma p230_rotated_continue base n y:
 Program230Histories.program230_step M p230_instruction_formula
 (cfg base(program230_path_value M(P++[true;true]))n y)
 (cfg base(program230_path_value M P)n y).
Proof.
 eapply(p230_rotated_literal M(P++[true;true])(P++[true;true])(EContinue 2));[reflexivity|apply p230_rotated_read|reflexivity|reflexivity|].
 cbn[program230_edge_step];split;[reflexivity|].
 intros i Hi;unfold p230_rotated_state;rewrite !program230_transfer_register by exact Hi;reflexivity.
Qed.
Lemma p230_rotated_zero base y:
 exists b c,program230_history M p230_instruction_formula b c(N 2)
 (cfg base(program230_path_value M P)Z y) /\
 program230_state_at M b c(N 2)(cfg base(program230_path_value M p230_rotated_exit)Z(S y)).
Proof.
 destruct(program230_history_one M p230_instruction_formula _ _(p230_rotated_inc base Z y))as[b[c[HR HT]]].
 destruct(program230_history_extend M p230_instruction_formula b c(N 1)_ _ _ HR HT
  (p230_rotated_dec_zero base(S y)))as[d[e[HR' [HT' _]]]].
 exists d,e;exact(conj HR' HT').
Qed.
Lemma p230_rotated_three base n y:
 exists b c,program230_history M p230_instruction_formula b c(N 3)
 (cfg base(program230_path_value M P)(S n)y) /\
 program230_state_at M b c(N 3)(cfg base(program230_path_value M P)n(S y)).
Proof.
 destruct(program230_history_one M p230_instruction_formula _ _(p230_rotated_inc base(S n)y))as[b[c[HR HT]]].
 destruct(program230_history_extend M p230_instruction_formula b c(N 1)_ _ _ HR HT
  (p230_rotated_dec_positive base n(S y)))as[d[e[HR' [HT' _]]]].
 destruct(program230_history_extend M p230_instruction_formula d e(N 2)_ _ _ HR' HT'
  (p230_rotated_continue base n(S y)))as[f[g[HR'' [HT'' _]]]].
 exists f,g;exact(conj HR'' HT'').
Qed.
End FiniteSteps.

Definition p230_rotated_property M base n:=forall y,exists b c,
 program230_history M p230_instruction_formula b c(p230_rotated_time M n)
 (p230_rotated_state base(program230_path_value M p230_rotated_path)n y) /\
 program230_state_at M b c(p230_rotated_time M n)
 (p230_rotated_state base(program230_path_value M p230_rotated_exit)(zeroM M)
  (addM M(addM M y n)(code_numeral M 1))).
Definition p230_rotated_parameters:program230_configuration term:=program230_config_of(fun j=>$ (4+j)).
Definition p230_rotated_property_formula:form:=∀∃∃
 (program230_history_formula p230_instruction_formula $1 $0(num 3⊗$3⊕num 2)
  (p230_rotated_state p230_rotated_parameters(program230_path_term p230_rotated_path)$3 $2) ∧
 program230_state_at_formula $1 $0(num 3⊗$3⊕num 2)
  (p230_rotated_state p230_rotated_parameters(program230_path_term p230_rotated_exit)zero($2⊕$3⊕num 1))).
Lemma p230_rotated_parameters_eval M base n y b c:
 program230_eval_config M(c.:b.:y.:n.:program230_field base)p230_rotated_parameters=base.
Proof.
 apply p230_configuration_ext;intros j Hj;rewrite program230_eval_field by exact Hj.
 unfold p230_rotated_parameters;rewrite program230_config_of_fields by exact Hj;reflexivity.
Qed.
Local Opaque holds program230_history_formula program230_state_at_formula program230_transfer_state.
Lemma p230_rotated_property_definable M base:Definable1 M(p230_rotated_property M base).
Proof.
 exists p230_rotated_property_formula,(program230_field base);intro n.
 unfold p230_rotated_property_formula,p230_rotated_property,p230_rotated_state.
 rewrite holds_all;repeat setoid_rewrite holds_ex;setoid_rewrite holds_and.
 setoid_rewrite program230_history_formula_correct;setoid_rewrite program230_state_at_formula_correct.
 setoid_rewrite program230_transfer_eval;setoid_rewrite p230_rotated_parameters_eval.
 setoid_rewrite program230_path_term_correct;unfold p230_rotated_time;reflexivity.
Qed.
Section Induction.
Variable M:Model.
Add Ring rotated_restore_ring:(model_semiring M).
Theorem p230_rotated_restore_uniform base n:p230_rotated_property M base n.
Proof.
 apply(definable_induction M(p230_rotated_property M base)(p230_rotated_property_definable M base)).
 -intro y;destruct(p230_rotated_zero M base y)as[b[c[HR HT]]].
  exists b,c;unfold p230_rotated_time.
  replace(addM M(mulM M(code_numeral M 3)(zeroM M))(code_numeral M 2))with(code_numeral M 2)
   by ring.
  rewrite coding_add_zero_r;replace(addM M y(code_numeral M 1))with(succM M y)by(apply succ_as_add).
  exact(conj HR HT).
 -intros k IH y.
  destruct(p230_rotated_three M base k y)as[b[c[HR HT]]].
  destruct(IH(succM M y))as[d[e[HI HTI]]].
  destruct(program230_history_join M p230_instruction_formula b c(code_numeral M 3)
   d e(p230_rotated_time M k)
   (p230_rotated_state base(program230_path_value M p230_rotated_path)(succM M k)y)
   (p230_rotated_state base(program230_path_value M p230_rotated_path)k(succM M y))HR HT HI)
   as[f[g[HJ[HL HTJ]]]].
  assert(ET:addM M(code_numeral M 3)(p230_rotated_time M k)=p230_rotated_time M(succM M k)).
  {unfold p230_rotated_time;rewrite(succ_as_add M k);ring. }
  assert(EV:addM M(addM M(succM M y)k)(code_numeral M 1)=addM M(addM M y(succM M k))(code_numeral M 1)).
  {rewrite(succ_as_add M y),(succ_as_add M k);ring. }
  exists f,g;split;[now rewrite <-ET|].
  rewrite <-ET,<-EV;apply(HTJ(p230_rotated_time M k)_ (coding_lt_succ M(p230_rotated_time M k)));exact HTI.
Qed.
End Induction.
Print Assumptions p230_rotated_zero.
Print Assumptions p230_rotated_three.
Print Assumptions p230_rotated_property_definable.
Print Assumptions p230_rotated_restore_uniform.
