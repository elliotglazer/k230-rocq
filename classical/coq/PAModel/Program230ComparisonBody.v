(** Complete actual comparison loop, including the residual-transfer branch. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
 Program230Configurations Program230Histories Program230HistoryJoin Program230HistoryConstructors
 Program230PathCode Program230InstructionFormula Program230TransferLoop Program230TransferProgram
 Program230RootHistory Program230ComparisonArithmetic Program230ComparisonIteration
 Program230ComparisonSites Program230ComparisonControl.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Bool.Bool Lia setoid_ring.Ring.
Import ListNotations.
Unset Implicit Arguments.

Section Site.
Variables (P:list bool) (n a b c d e:nat).
Hypothesis occurrence:p230_comparison_occurrence p230 P n a b c d e.
Variable M:Model.
Local Notation Z := (zeroM M).
Local Notation S := (succM M).
Local Notation N := (code_numeral M).
Local Infix "+" := (addM M).
Local Notation cfg := program230_comparison_state.
Add Ring comparison_body_ring : (model_semiring M).

Lemma comparison_residual_transfer base x:
 exists u v,program230_history M p230_instruction_formula u v (program230_transfer_time M x)
 (cfg base (program230_path_value M (P++[true;true])) x Z) /\
 program230_state_at M u v (program230_transfer_time M x)
 (cfg base (program230_path_value M (P++[true;true;true])) Z x).
Proof.
 set (start:=cfg base (program230_path_value M (P++[true;true;false])) x Z).
 assert (HX:program230_register start 6=x) by (unfold start;rewrite comparison_register by lia;reflexivity).
 destruct (program230_transfer_program_history M p230 (P++[true;true;false]) 6 5 d e start x
  ltac:(lia) ltac:(lia) ltac:(lia)
  (comparison_transfer_occurrence P n a b c d e occurrence)
  eq_refl HX) as [u [v [last [HR [HT [Hpc [H6 [H5 Hframe]]]]]]]].
 apply (proj2 (p230_instruction_history_correct M u v (program230_transfer_time M x) start)) in HR.
 assert (E:last=cfg base (program230_path_value M (P++[true;true;true])) Z x).
 { apply p230_configuration_ext;intros j Hj;destruct j as [|j].
   -change (program230_pc last=program230_path_value M (P++[true;true;true])).
    rewrite Hpc.
    replace (P++[true;true;false]) with ((P++[true;true])++[false]) by (rewrite <-app_assoc;reflexivity).
    rewrite inc_path_app_false,<-app_assoc;reflexivity.
   -change (program230_register last j=program230_register (cfg base (program230_path_value M (P++[true;true;true])) Z x) j).
    rewrite comparison_register by lia.
    unfold start in H5,Hframe;rewrite comparison_register in H5 by lia;cbn [Nat.eqb] in H5.
    rewrite coding_add_zero in H5.
    do 9 (destruct j as [|j];[cbn [Nat.eqb];first [exact H6|exact H5|rewrite Hframe by lia;rewrite comparison_register by lia;reflexivity]|]);lia. }
 subst last.
 assert (Hnz:program230_transfer_time M x<>Z).
 { unfold program230_transfer_time;change ((mulM M (N 3) x)+S Z<>Z).
   rewrite <-(succ_as_add M (mulM M (N 3) x));intro H;apply (zero_ne_succ M (mulM M (N 3) x));symmetry;exact H. }
 assert (HE:ipeq (P++[true;true;false]) (P++[true;true])).
 { replace (P++[true;true;false]) with ((P++[true;true])++[false]) by (rewrite <-app_assoc;reflexivity).
   apply ipeq_app_false. }
 destruct (p230_history_ipeq_endpoint M u v (program230_transfer_time M x) start
   (P++[true;true;false]) (P++[true;true])
   (cfg base (program230_path_value M (P++[true;true;true])) Z x)
   eq_refl HE HR Hnz HT) as [f [g [HF [HG _]]]].
 exists f,g;split;[|exact HG].
 change (program230_history M p230_instruction_formula f g (program230_transfer_time M x)
  (program230_with_pc start (program230_path_value M (P++[true;true])))).
 exact HF.
Qed.

Theorem comparison_actual_leftover:program230_comparison_leftover_exit M P (inc_path P).
Proof.
 intros base x.
 destruct (program230_history_one M p230_instruction_formula _ _
  (comparison_left_positive P n a b c d e occurrence M base x Z)) as [u [v [HR HT]]].
 destruct (program230_history_extend M p230_instruction_formula u v (N 1) _ _ _ HR HT
  (comparison_right_zero P n a b c d e occurrence M base x)) as [f [g [HF [HG _]]]].
 destruct (comparison_residual_transfer base x) as [r [s [HK HL]]].
 destruct (program230_history_join M p230_instruction_formula f g (N 2) r s
  (program230_transfer_time M x) _ _ HF HG HK) as [h [i [HH [Hpre Hpost]]]].
 pose proof (proj1 (Hpost (program230_transfer_time M x) _ (coding_lt_succ M (program230_transfer_time M x))) HL) as Hlast.
 destruct (program230_history_extend M p230_instruction_formula h i
  ((N 2)+program230_transfer_time M x) _ _ _ HH Hlast
  (comparison_final_increment P n a b c d e occurrence M base x)) as [j [k [HJ [HKlast _]]]].
 assert (ET:S ((N 2)+program230_transfer_time M x)=program230_comparison_time M (S x)).
 { unfold program230_transfer_time,program230_comparison_time.
   rewrite (succ_as_add M ((N 2)+(mulM M (N 3) x+(N 1)))),(succ_as_add M x).
   assert (E3:N 3=(N 2)+(N 1)) by (apply succ_as_add).
   rewrite E3.
   change (((N 2)+(mulM M ((N 2)+S Z) x+S Z))+S Z=
     mulM M ((N 2)+S Z) (x+S Z)+S Z).
   ring. }
 exists j,k;rewrite <-ET;split;assumption.
Qed.

Theorem comparison_actual_loop base x:
 program230_comparison_property M P (inc_path P) base x.
Proof.
 apply (program230_comparison_induction M P (inc_path P)).
 -exact (comparison_actual_cycle P n a b c d e occurrence M).
 -exact (comparison_actual_zero_exit P n a b c d e occurrence M).
 -exact comparison_actual_leftover.
Qed.
End Site.

Theorem p230_comparison_loop_0 M base x:
 program230_comparison_property M p230_comparison_path_0 (inc_path p230_comparison_path_0) base x.
Proof. exact (comparison_actual_loop p230_comparison_path_0 4954 4955 4956 4957 4958 4959 p230_comparison_site_0 M base x). Qed.
Theorem p230_comparison_loop_1 M base x:
 program230_comparison_property M p230_comparison_path_1 (inc_path p230_comparison_path_1) base x.
Proof. exact (comparison_actual_loop p230_comparison_path_1 4971 4972 4973 4974 4975 4976 p230_comparison_site_1 M base x). Qed.
Theorem p230_comparison_loop_2 M base x:
 program230_comparison_property M p230_comparison_path_2 (inc_path p230_comparison_path_2) base x.
Proof. exact (comparison_actual_loop p230_comparison_path_2 4985 4986 4987 4988 4989 4990 p230_comparison_site_2 M base x). Qed.
Theorem p230_comparison_loop_3 M base x:
 program230_comparison_property M p230_comparison_path_3 (inc_path p230_comparison_path_3) base x.
Proof. exact (comparison_actual_loop p230_comparison_path_3 5090 5091 5092 5093 5094 5095 p230_comparison_site_3 M base x). Qed.
Print Assumptions comparison_actual_loop.
Print Assumptions p230_comparison_loop_0.
Print Assumptions p230_comparison_loop_1.
Print Assumptions p230_comparison_loop_2.
Print Assumptions p230_comparison_loop_3.
