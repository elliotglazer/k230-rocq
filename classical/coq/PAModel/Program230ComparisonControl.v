(** Actual three-step positive cycle and zero exit at all comparison sites. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
 Program230Configurations Program230Histories Program230HistoryConstructors
 Program230PathCode Program230Read Program230Walk Program230Edges Program230Transition
 Program230InstructionFormula Program230TransferProgram Program230ComparisonIteration
 Program230ComparisonSites.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Bool.Bool Lia.
Import ListNotations.
Unset Implicit Arguments.

Lemma comparison_read_zeros M P n:
 program230_read M (program230_path_value M P) (P++repeat false n) (succM M (zeroM M)).
Proof.
 apply program230_read_app;exists (succM M (zeroM M));split;[apply program230_read_exact_path|].
 induction n as [|n IH];[reflexivity|]. cbn [repeat program230_read].
 exists (succM M (zeroM M));split;[left;repeat split;reflexivity|exact IH].
Qed.
Lemma comparison_literal M P Q e s t:
 program230_pc s=program230_path_value M P ->
 program230_read M (program230_path_value M P) Q (succM M (zeroM M)) ->
 fol p230 (ENode (root p230)) Q=Some e -> is_node e=false ->
 program230_edge_step M Q e (program230_register s) (program230_register t) (program230_pc t) ->
 Program230Histories.program230_step M p230_instruction_formula s t.
Proof.
 intros HP HR HF HE HS;apply p230_instruction_formula_correct.
 exists e,Q,(succM M (zeroM M));split;[split;[now rewrite HP|split;assumption]|exact HS].
Qed.
Lemma comparison_register {D} (base:program230_configuration D) pc x y i:
 (i<9)%nat -> program230_register (program230_comparison_state base pc x y) i=
 if Nat.eqb i 6 then x else if Nat.eqb i 5 then y else program230_register base i.
Proof. intro Hi;do 9 (destruct i as [|i];[reflexivity|]);lia. Qed.

Section Site.
Variables (P:list bool) (n a b c d e:nat).
Hypothesis occurrence:p230_comparison_occurrence p230 P n a b c d e.
Lemma comparison_leaves:
 fol p230 (ENode(root p230)) (P++[false])=Some(EDecnz 6) /\
 fol p230 (ENode(root p230)) (P++[true;false;false])=Some(EDecnz 5) /\
 fol p230 (ENode(root p230)) (P++[true;false;true])=Some(EContinue 2).
Proof.
 destruct occurrence as [HP [HN [HA [HB [HC [HD HE]]]]]].
 rewrite !fol_app,HP;cbn [fol child];rewrite HN;cbn [fst snd fol child];rewrite HA;
 cbn [fst snd fol child];rewrite HB;repeat split;reflexivity.
Qed.
Variable M:Model.
Local Notation Z := (zeroM M).
Local Notation S := (succM M).
Local Notation cfg := program230_comparison_state.
Local Ltac fields := intros i Hi;rewrite !comparison_register by exact Hi;
 do 9 (destruct i as [|i];[reflexivity|]);lia.

Lemma comparison_zero_step base y:
 Program230Histories.program230_step M p230_instruction_formula
  (cfg base (program230_path_value M P) Z y)
  (cfg base (program230_path_value M (inc_path P)) Z y).
Proof.
 eapply (comparison_literal M P (P++[false]) (EDecnz 6));
 [reflexivity|apply program230_read_path_zero|exact (proj1 comparison_leaves)|reflexivity|].
 cbn [program230_edge_step];split;[lia|];left;split.
 -rewrite comparison_register by lia;reflexivity.
 -split;[rewrite p230_comparison_left_exit;reflexivity|fields].
Qed.
Lemma comparison_left_positive base x y:
 Program230Histories.program230_step M p230_instruction_formula
  (cfg base (program230_path_value M P) (S x) y)
  (cfg base (program230_path_value M (P++[true])) x y).
Proof.
 eapply (comparison_literal M P (P++[false]) (EDecnz 6));
 [reflexivity|apply program230_read_path_zero|exact (proj1 comparison_leaves)|reflexivity|].
 cbn [program230_edge_step];split;[lia|];right;exists x;split.
 -rewrite comparison_register by lia;reflexivity.
 -split;[rewrite inc_path_app_false;reflexivity|fields].
Qed.
Lemma comparison_right_positive base x y:
 Program230Histories.program230_step M p230_instruction_formula
  (cfg base (program230_path_value M (P++[true])) x (S y))
  (cfg base (program230_path_value M (P++[true;false;true])) x y).
Proof.
 eapply (comparison_literal M (P++[true]) (P++[true;false;false]) (EDecnz 5));
 [reflexivity| |exact (proj1(proj2 comparison_leaves))|reflexivity|].
 -replace (P++[true;false;false]) with ((P++[true])++repeat false 2) by (rewrite <-app_assoc;reflexivity).
  apply comparison_read_zeros.
 -cbn [program230_edge_step];split;[lia|];right;exists y;split.
  +rewrite comparison_register by lia;reflexivity.
  +split;[|fields].
   replace (P++[true;false;false]) with ((P++[true;false])++[false]) by (rewrite <-app_assoc;reflexivity).
   rewrite inc_path_app_false,<-app_assoc;reflexivity.
Qed.
Lemma comparison_continue base x y:
 Program230Histories.program230_step M p230_instruction_formula
  (cfg base (program230_path_value M (P++[true;false;true])) x y)
  (cfg base (program230_path_value M P) x y).
Proof.
 eapply (comparison_literal M (P++[true;false;true]) (P++[true;false;true]) (EContinue 2));
 [reflexivity|apply program230_read_exact_path|exact (proj2(proj2 comparison_leaves))|reflexivity|].
 cbn [program230_edge_step];split;[rewrite p230_comparison_cycle_return;reflexivity|fields].
Qed.

Lemma comparison_right_zero base x:
 Program230Histories.program230_step M p230_instruction_formula
  (cfg base (program230_path_value M (P++[true])) x Z)
  (cfg base (program230_path_value M (P++[true;true])) x Z).
Proof.
 eapply (comparison_literal M (P++[true]) (P++[true;false;false]) (EDecnz 5));
 [reflexivity| |exact (proj1(proj2 comparison_leaves))|reflexivity|].
 -replace (P++[true;false;false]) with ((P++[true])++repeat false 2) by (rewrite <-app_assoc;reflexivity).
  apply comparison_read_zeros.
 -cbn [program230_edge_step];split;[lia|];left;split.
  +rewrite comparison_register by lia;reflexivity.
  +split;[|fields].
   replace (P++[true;false;false]) with ((P++[true;false])++[false]) by (rewrite <-app_assoc;reflexivity).
   rewrite brk_car1.
   replace (P++[true;false]) with ((P++[true])++[false]) by (rewrite <-app_assoc;reflexivity).
   rewrite inc_path_app_false,<-app_assoc;reflexivity.
Qed.

Lemma comparison_transfer_occurrence:
 program230_transfer_occurrence p230 (P++[true;true;false]) 6 5 d e.
Proof.
 destruct occurrence as [HP [HN [HA [HB [HC [HD HE]]]]]].
 unfold program230_transfer_occurrence;split;[|auto].
 rewrite fol_app,HP;cbn [fol child];rewrite HN;cbn [fst snd fol child];rewrite HA;
 cbn [fst snd fol child];rewrite HC;reflexivity.
Qed.

Lemma comparison_final_increment base y:
 Program230Histories.program230_step M p230_instruction_formula
  (cfg base (program230_path_value M (P++[true;true;true])) Z y)
  (cfg base (program230_path_value M (inc_path P++[false;false;false])) Z (S y)).
Proof.
 eapply (comparison_literal M (P++[true;true;true]) (P++[true;true;true]) (EInc 5));
 [reflexivity|apply program230_read_exact_path| |reflexivity|].
 -destruct occurrence as [HP [HN [HA [HB [HC [HD HE]]]]]].
  rewrite fol_app,HP;cbn [fol child];rewrite HN;cbn [fst snd fol child];rewrite HA;
  cbn [fst snd fol child];rewrite HC;reflexivity.
 -cbn [program230_edge_step];split;[lia|];split.
  +rewrite p230_comparison_right_exit;reflexivity.
  +rewrite comparison_register by lia;fields.
Qed.

Theorem comparison_actual_zero_exit:program230_comparison_zero_exit M P (inc_path P).
Proof.
 intros base y;exact (program230_history_one M p230_instruction_formula _ _ (comparison_zero_step base y)).
Qed.
Theorem comparison_actual_cycle:program230_comparison_cycle M P.
Proof.
 intros base x y.
 destruct (program230_history_one M p230_instruction_formula _ _ (comparison_left_positive base x (S y)))
  as [u [v [HR HT]]].
 destruct (program230_history_extend M p230_instruction_formula u v (code_numeral M 1)
  _ _ _ HR HT (comparison_right_positive base x y)) as [w [z [HQ [HU _]]]].
 destruct (program230_history_extend M p230_instruction_formula w z (code_numeral M 2)
  _ _ _ HQ HU (comparison_continue base x y)) as [f [g [HK [HV _]]]].
 exists f,g;split;assumption.
Qed.
End Site.
Print Assumptions comparison_actual_zero_exit.
Print Assumptions comparison_actual_cycle.
