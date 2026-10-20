(** Actual NIP halting branch: a clean scratch counter and h=1 reach EHalt. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaPacking
 CodeExpressions NumericalProofs Program230Configurations Program230Histories
 Program230HistoryJoin Program230HistoryConstructors Program230InstructionFormula
 Program230HaltingSentence Program230Transition Program230PathCode Program230Edges
 Program230TransferProgram Program230RootHistory Program230Selector
 Program230ComparisonIteration Program230ComparisonControl Program230ComparisonGuards
 Program230EqualitySites Program230NipHaltSite.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.

Lemma p230_nip_comparison_parent:p230_comparison_parent_path_2=p230_nip_test_parent.
Proof. reflexivity. Qed.

Theorem p230_nip_test_reaches_halt M base x:
 exists b c time,program230_history M p230_instruction_formula b c time
 (program230_comparison_state base (program230_path_value M p230_nip_test_parent) x x) /\
 p230_counter_halt_at M b c time /\coding_lt M (zeroM M) time.
Proof.
 destruct (proj1 (p230_equality_site_histories M p230_comparison_parent_path_2 base x x equality_site_2) eq_refl)
  as [b [c [time [HR [HT Hpos]]]]].
 rewrite p230_nip_comparison_parent in HR,HT.
 exists b,c,time;split;[exact HR|split;[|exact Hpos]].
 exists (program230_comparison_state base (program230_path_value M p230_nip_equal_exit) (zeroM M) (zeroM M)).
 split;[exact HT|exact (p230_nip_equal_halts M)].
Qed.

Lemma p230_nip_increment M base h:
 Program230Histories.program230_step M p230_instruction_formula
 (program230_comparison_state base (program230_path_value M p230_selector_nip)
  (zeroM M) h)
 (program230_comparison_state base (program230_path_value M (p230_selector_nip++[true]))
  (code_numeral M 1) h).
Proof.
 eapply (comparison_literal M p230_selector_nip (p230_selector_nip++[false]) (EInc 6));
 [reflexivity|apply program230_read_path_zero|reflexivity|reflexivity|].
 cbn [program230_edge_step];split;[lia|];split.
 -rewrite inc_path_app_false;reflexivity.
 -rewrite comparison_register by lia.
  intros i Hi;rewrite !comparison_register by exact Hi.
  do 9 (destruct i as [|i];[reflexivity|]);lia.
Qed.

Theorem p230_nip_action_reaches_halt M base:
 exists b c time,program230_history M p230_instruction_formula b c time
 (program230_comparison_state base (program230_path_value M p230_selector_nip)
  (zeroM M) (code_numeral M 1)) /\
 p230_counter_halt_at M b c time /\coding_lt M (zeroM M) time.
Proof.
 destruct (p230_nip_test_reaches_halt M base (code_numeral M 1))
  as [b [c [time [HR [[last [HT HH]] Hpos]]]]].
 assert (HP:ipeq p230_nip_test_parent (p230_selector_nip++[true])).
 { change (ipeq (((p230_selector_nip++[true])++[false])++[false]) (p230_selector_nip++[true])).
   eapply ipeq_trans;apply ipeq_app_false. }
 assert (HN:time<>zeroM M) by
  (intro E;rewrite E in Hpos;exact (coding_not_lt_zero M (zeroM M) Hpos)).
 destruct (p230_history_ipeq_endpoint M b c time
  (program230_comparison_state base (program230_path_value M p230_nip_test_parent)
    (code_numeral M 1) (code_numeral M 1))
  p230_nip_test_parent (p230_selector_nip++[true]) last eq_refl HP HR HN HT)
  as [d [e [HD [HE _]]]].
 destruct (program230_history_one M p230_instruction_formula _ _ (p230_nip_increment M base (code_numeral M 1)))
  as [f [g [HF HG]]].
 change (program230_history M p230_instruction_formula d e time
  (program230_comparison_state base (program230_path_value M (p230_selector_nip++[true]))
    (code_numeral M 1) (code_numeral M 1))) in HD.
 destruct (program230_history_join M p230_instruction_formula f g (code_numeral M 1) d e time
  _ _ HF HG HD) as [u [v [HU [Hpre Hpost]]]].
 exists u,v,(addM M (code_numeral M 1) time);split;[exact HU|split].
 -exists last;split;[|exact HH].
  exact (proj1 (Hpost time last (coding_lt_succ M time)) HE).
 -pose proof (coding_lt_add_left M (code_numeral M 1) (zeroM M) time Hpos) as Hplus.
  rewrite coding_add_zero_r in Hplus.
  exact (coding_lt_trans M (zeroM M) (code_numeral M 1)
    (addM M (code_numeral M 1) time) (coding_lt_succ M (zeroM M)) Hplus).
Qed.

Theorem p230_nip_skip_halt M base h:h<>code_numeral M 1 ->
 exists b c time,program230_history M p230_instruction_formula b c time
 (program230_comparison_state base (program230_path_value M p230_selector_nip) (zeroM M) h) /\
 program230_state_at M b c time
 (program230_comparison_state base (program230_path_value M p230_nip_unequal_exit) (zeroM M) (zeroM M)) /\
 coding_lt M (zeroM M) time.
Proof.
 intro Hh.
 assert (Hneq:code_numeral M 1<>h) by (intro E;apply Hh;symmetry;exact E).
 destruct (proj2 (p230_equality_site_histories M p230_comparison_parent_path_2 base
   (code_numeral M 1) h equality_site_2) Hneq) as [b [c [time [HR [HT Hpos]]]]].
 rewrite p230_nip_comparison_parent in HR,HT.
 assert (HP:ipeq p230_nip_test_parent (p230_selector_nip++[true])).
 { change (ipeq (((p230_selector_nip++[true])++[false])++[false]) (p230_selector_nip++[true])).
   eapply ipeq_trans;apply ipeq_app_false. }
 assert (HN:time<>zeroM M) by
  (intro E;rewrite E in Hpos;exact (coding_not_lt_zero M (zeroM M) Hpos)).
 destruct (p230_history_ipeq_endpoint M b c time
   (program230_comparison_state base (program230_path_value M p230_nip_test_parent) (code_numeral M 1) h)
   p230_nip_test_parent (p230_selector_nip++[true])
   (program230_comparison_state base (program230_path_value M p230_nip_unequal_exit) (zeroM M) (zeroM M))
   eq_refl HP HR HN HT) as [d [e [HD [HE _]]]].
 destruct (program230_history_one M p230_instruction_formula _ _ (p230_nip_increment M base h))
  as [f [g [HF HG]]].
 change (program230_history M p230_instruction_formula d e time
  (program230_comparison_state base (program230_path_value M (p230_selector_nip++[true]))
    (code_numeral M 1) h)) in HD.
 destruct (program230_history_join M p230_instruction_formula f g (code_numeral M 1) d e time
   _ _ HF HG HD) as [u [v [HU [Hpre Hpost]]]].
 exists u,v,(addM M (code_numeral M 1) time);split;[exact HU|split].
 -exact (proj1 (Hpost time _ (coding_lt_succ M time)) HE).
 -pose proof (coding_lt_add_left M (code_numeral M 1) (zeroM M) time Hpos) as Hplus.
  rewrite coding_add_zero_r in Hplus.
  exact (coding_lt_trans M (zeroM M) (code_numeral M 1)
    (addM M (code_numeral M 1) time) (coding_lt_succ M (zeroM M)) Hplus).
Qed.
Print Assumptions p230_nip_test_reaches_halt.
Print Assumptions p230_nip_action_reaches_halt.
Print Assumptions p230_nip_skip_halt.
