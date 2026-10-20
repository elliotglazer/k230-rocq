(** Actual equality-test guard and residual clearing after comparison. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
 Program230Configurations Program230Histories Program230HistoryJoin Program230HistoryConstructors
 Program230PathCode Program230InstructionFormula Program230Edges Program230TransferProgram
 Program230ResetLoop Program230RootHistory Program230ComparisonIteration
 Program230ComparisonControl Program230ComparisonGuards.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Bool.Bool Lia setoid_ring.Ring.
Import ListNotations.
Unset Implicit Arguments.

Section Guard.
Variables (P:list bool) (parent loop guard wrapper reset:nat).
Hypothesis site:p230_comparison_guard_occurrence p230 P parent loop guard wrapper reset.
Lemma equality_guard_leaves:
 fol p230 (ENode(root p230)) (P++[true;false])=Some(EDecnz 5) /\
 fol p230 (ENode(root p230)) (P++[true;true;true])=Some(EBreak 1).
Proof.
 destruct site as [HP [HA [HB [HC HD]]]].
 rewrite !fol_app,HP;cbn [fol child];rewrite HA;cbn [fst snd fol child];rewrite HB;
 cbn [fst snd fol child];rewrite HC;split;reflexivity.
Qed.
Lemma equality_reset_occurrence:
 program230_reset_occurrence p230 (P++[true;true;false]) 5 reset.
Proof.
 destruct site as [HP [HA [HB [HC HD]]]].
 unfold program230_reset_occurrence;split;[|exact HD].
 rewrite fol_app,HP;cbn [fol child];rewrite HA;cbn [fst snd fol child];rewrite HB;
 cbn [fst snd fol child];rewrite HC;reflexivity.
Qed.
Variable M:Model.
Local Notation Z := (zeroM M).
Local Notation S := (succM M).
Local Notation N := (code_numeral M).
Local Infix "+" := (addM M).
Local Notation cfg := program230_comparison_state.
Add Ring equality_guard_ring : (model_semiring M).
Local Ltac fields := intros i Hi;rewrite !comparison_register by exact Hi;
 do 9 (destruct i as [|i];[reflexivity|]);lia.

Lemma equality_guard_zero_step base:
 Program230Histories.program230_step M p230_instruction_formula
 (cfg base (program230_path_value M (P++[true])) Z Z)
 (cfg base (program230_path_value M (inc_path P++[false])) Z Z).
Proof.
 eapply (comparison_literal M (P++[true]) (P++[true;false]) (EDecnz 5));
 [reflexivity| |exact (proj1 equality_guard_leaves)|reflexivity|].
 -replace (P++[true;false]) with ((P++[true])++[false]) by (rewrite <-app_assoc;reflexivity).
  apply program230_read_path_zero.
 -cbn [program230_edge_step];split;[lia|];left;split.
  +rewrite comparison_register by lia;reflexivity.
  +split;[rewrite p230_comparison_guard_equal_exit;reflexivity|fields].
Qed.
Lemma equality_guard_positive_step base y:
 Program230Histories.program230_step M p230_instruction_formula
 (cfg base (program230_path_value M (P++[true])) Z (S y))
 (cfg base (program230_path_value M (P++[true;true])) Z y).
Proof.
 eapply (comparison_literal M (P++[true]) (P++[true;false]) (EDecnz 5));
 [reflexivity| |exact (proj1 equality_guard_leaves)|reflexivity|].
 -replace (P++[true;false]) with ((P++[true])++[false]) by (rewrite <-app_assoc;reflexivity).
  apply program230_read_path_zero.
 -cbn [program230_edge_step];split;[lia|];right;exists y;split.
  +rewrite comparison_register by lia;reflexivity.
  +split;[|fields].
   replace (P++[true;false]) with ((P++[true])++[false]) by (rewrite <-app_assoc;reflexivity).
   rewrite inc_path_app_false,<-app_assoc;reflexivity.
Qed.
Lemma equality_guard_break_step base:
 Program230Histories.program230_step M p230_instruction_formula
 (cfg base (program230_path_value M (P++[true;true;true])) Z Z)
 (cfg base (program230_path_value M (brk 1 P)) Z Z).
Proof.
 eapply (comparison_literal M (P++[true;true;true]) (P++[true;true;true]) (EBreak 1));
 [reflexivity|apply program230_read_exact_path|exact (proj2 equality_guard_leaves)|reflexivity|].
 cbn [program230_edge_step];split;[rewrite p230_comparison_guard_unequal_exit;reflexivity|fields].
Qed.

Lemma equality_guard_reset base y:
 exists b c,program230_history M p230_instruction_formula b c (program230_reset_time M y)
 (cfg base (program230_path_value M (P++[true;true])) Z y) /\
 program230_state_at M b c (program230_reset_time M y)
 (cfg base (program230_path_value M (P++[true;true;true])) Z Z).
Proof.
 set (start:=cfg base (program230_path_value M (P++[true;true;false])) Z y).
 assert (HY:program230_register start 5=y) by (unfold start;rewrite comparison_register by lia;reflexivity).
 destruct (program230_reset_program_history M p230 (P++[true;true;false]) 5 reset start y
   ltac:(lia) equality_reset_occurrence eq_refl HY)
   as [b [c [last [HR [HT [Hpc [H5 Hframe]]]]]]].
 apply (proj2 (p230_instruction_history_correct M b c (program230_reset_time M y) start)) in HR.
 assert (E:last=cfg base (program230_path_value M (P++[true;true;true])) Z Z).
 { apply p230_configuration_ext;intros j Hj;destruct j as [|j].
   -change (program230_pc last=program230_path_value M (P++[true;true;true])).
    rewrite Hpc,p230_comparison_guard_reset_exit;reflexivity.
   -change (program230_register last j=program230_register (cfg base (program230_path_value M (P++[true;true;true])) Z Z) j).
    rewrite comparison_register by lia;unfold start in Hframe.
    do 9 (destruct j as [|j];[cbn [Nat.eqb];first [exact H5|rewrite Hframe by lia;rewrite comparison_register by lia;reflexivity]|]);lia. }
 subst last.
 assert (Hnz:program230_reset_time M y<>Z).
 { unfold program230_reset_time;change (mulM M (N 2) y+S Z<>Z).
   rewrite <-(succ_as_add M (mulM M (N 2) y));intro H;apply (zero_ne_succ M (mulM M (N 2) y));symmetry;exact H. }
 assert (HP:ipeq (P++[true;true;false]) (P++[true;true])).
 { replace (P++[true;true;false]) with ((P++[true;true])++[false]) by (rewrite <-app_assoc;reflexivity).
   apply ipeq_app_false. }
 destruct (p230_history_ipeq_endpoint M b c (program230_reset_time M y) start
   (P++[true;true;false]) (P++[true;true])
   (cfg base (program230_path_value M (P++[true;true;true])) Z Z)
   eq_refl HP HR Hnz HT) as [f [g [HF [HG _]]]].
 exists f,g;split;[|exact HG].
 change (program230_history M p230_instruction_formula f g (program230_reset_time M y)
  (program230_with_pc start (program230_path_value M (P++[true;true]))));exact HF.
Qed.

Theorem equality_guard_equal_history base:
 exists b c,program230_history M p230_instruction_formula b c (N 1)
 (cfg base (program230_path_value M (P++[true])) Z Z) /\
 program230_state_at M b c (N 1) (cfg base (program230_path_value M (inc_path P++[false])) Z Z).
Proof. exact (program230_history_one M p230_instruction_formula _ _ (equality_guard_zero_step base)). Qed.
Theorem equality_guard_unequal_history base y:
 exists b c,program230_history M p230_instruction_formula b c
  (S (N 1+program230_reset_time M y))
 (cfg base (program230_path_value M (P++[true])) Z (S y)) /\
 program230_state_at M b c (S (N 1+program230_reset_time M y))
 (cfg base (program230_path_value M (brk 1 P)) Z Z).
Proof.
 destruct (program230_history_one M p230_instruction_formula _ _ (equality_guard_positive_step base y)) as [b [c [HR HT]]].
 destruct (equality_guard_reset base y) as [d [e [HD HE]]].
 destruct (program230_history_join M p230_instruction_formula b c (N 1) d e (program230_reset_time M y)
   _ _ HR HT HD) as [f [g [HF [Hpre Hpost]]]].
 pose proof (proj1 (Hpost (program230_reset_time M y) _ (coding_lt_succ M (program230_reset_time M y))) HE) as Hlast.
 destruct (program230_history_extend M p230_instruction_formula f g (N 1+program230_reset_time M y)
   _ _ _ HF Hlast (equality_guard_break_step base)) as [h [i [HH [HI _]]]].
 exists h,i;split;assumption.
Qed.
End Guard.
Print Assumptions equality_guard_equal_history.
Print Assumptions equality_guard_unequal_history.
