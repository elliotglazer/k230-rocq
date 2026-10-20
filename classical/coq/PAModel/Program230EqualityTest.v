(** Compose the verified comparison loop with the actual equality guard.
    The two finite certificates identify the literal source occurrence. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions NumericalProofs
 Program230Configurations Program230Histories Program230HistoryJoin
 Program230PathCode Program230InstructionFormula Program230RootHistory
 Program230ComparisonArithmetic Program230ComparisonIteration Program230ComparisonSites
 Program230ComparisonBody Program230ComparisonGuards Program230EqualityGuard.
From K230 Require Import RM RMEquiv Prog230.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import Lists.List Lia setoid_ring.Ring.
Import ListNotations.
Unset Implicit Arguments.

Section EqualityTest.
Variables (P:list bool) (parent loop guard wrapper reset node_a node_b node_c node_d node_e:nat).
Hypothesis Hguard:p230_comparison_guard_occurrence p230 P parent loop guard wrapper reset.
Hypothesis Hloop:p230_comparison_occurrence p230 (P++[false]) loop node_a node_b node_c node_d node_e.
Variable M:Model.
Local Notation Z := (zeroM M).
Local Notation S := (succM M).
Local Notation N := (code_numeral M).
Local Infix "+" := (addM M).
Local Notation cfg := program230_comparison_state.
Add Ring equality_test_ring : (model_semiring M).

Lemma equality_test_pad_guard base pc residual b c time last:
 program230_comparison_exit M (P++[true]) pc ->
 program230_history M p230_instruction_formula b c time
   (cfg base (program230_path_value M (P++[true])) Z residual) ->
 time<>Z ->program230_state_at M b c time last ->
 exists f g,program230_history M p230_instruction_formula f g time (cfg base pc Z residual) /\
 program230_state_at M f g time last.
Proof.
 intros [Hpc|Hpc] HR Hnz HT.
 -rewrite Hpc;exists b,c;auto.
 -rewrite Hpc.
  assert (HP:ipeq (P++[true]) ((P++[true])++[false;false;false])).
  { apply ipeq_sym.
    replace ((P++[true])++[false;false;false]) with ((((P++[true])++[false])++[false])++[false])
     by (rewrite <-!app_assoc;reflexivity).
    eapply ipeq_trans;[apply ipeq_app_false|].
    eapply ipeq_trans;[apply ipeq_app_false|apply ipeq_app_false]. }
  destruct (p230_history_ipeq_endpoint M b c time
    (cfg base (program230_path_value M (P++[true])) Z residual)
    (P++[true]) ((P++[true])++[false;false;false]) last eq_refl HP HR Hnz HT)
    as [f [g [HF [HG _]]]].
  exists f,g;split;[|exact HG].
  change (program230_history M p230_instruction_formula f g time
    (program230_with_pc (cfg base (program230_path_value M (P++[true])) Z residual)
      (program230_path_value M ((P++[true])++[false;false;false]))));exact HF.
Qed.
Lemma equality_test_positive_sum x y:coding_lt M Z (x+S y).
Proof.
 exists (x+y);rewrite coding_add_zero,(succ_as_add M y),(succ_as_add M (x+y));ring.
Qed.

Theorem equality_test_equal_history base x y:x=y ->
 exists b c time,program230_history M p230_instruction_formula b c time
  (cfg base (program230_path_value M P) x y) /\
 program230_state_at M b c time (cfg base (program230_path_value M (inc_path P++[false])) Z Z) /\
 coding_lt M Z time.
Proof.
 intro Hxy.
 destruct (comparison_actual_loop (P++[false]) loop node_a node_b node_c node_d node_e Hloop M base x y)
  as [residual [pc [u [v [HD [HE [HR HT]]]]]]].
 assert (HZ:residual=Z) by (exact (proj2 (program230_difference_zero_iff M x y residual HD) Hxy)).
 subst residual;rewrite inc_path_app_false in HE.
 destruct (equality_guard_equal_history P parent loop guard wrapper reset Hguard M base)
  as [f [g [HF HG]]].
 assert (Hnz:N 1<>Z) by (intro H;apply (zero_ne_succ M Z);symmetry;exact H).
 destruct (equality_test_pad_guard base pc Z f g (N 1)
  (cfg base (program230_path_value M (inc_path P++[false])) Z Z) HE HF Hnz HG)
  as [r [s [HK HL]]].
 destruct (program230_history_join M p230_instruction_formula u v (program230_comparison_time M x)
   r s (N 1) _ _ HR HT HK) as [j [k [HJ [Hpre Hpost]]]].
 set (time:=program230_comparison_time M x+N 1).
 pose proof (proj1 (Hpost (N 1) _ (coding_lt_succ M (N 1))) HL) as Hlast.
 assert (Hpos:coding_lt M Z time) by (apply equality_test_positive_sum).
 assert (Htime:time<>Z) by
  (intro H;rewrite H in Hpos;exact (coding_not_lt_zero M Z Hpos)).
 destruct (p230_history_ipeq_endpoint M j k time
   (cfg base (program230_path_value M (P++[false])) x y) (P++[false]) P
   (cfg base (program230_path_value M (inc_path P++[false])) Z Z)
   eq_refl (ipeq_app_false P) HJ Htime Hlast) as [p [q [HP [HQ _]]]].
 exists p,q,time;split;[|split;assumption].
 change (program230_history M p230_instruction_formula p q time
  (program230_with_pc (cfg base (program230_path_value M (P++[false])) x y)
    (program230_path_value M P)));exact HP.
Qed.

Theorem equality_test_unequal_history base x y:x<>y ->
 exists b c time,program230_history M p230_instruction_formula b c time
  (cfg base (program230_path_value M P) x y) /\
 program230_state_at M b c time (cfg base (program230_path_value M (brk 1 P)) Z Z) /\
 coding_lt M Z time.
Proof.
 intro Hxy.
 destruct (comparison_actual_loop (P++[false]) loop node_a node_b node_c node_d node_e Hloop M base x y)
  as [residual [pc [u [v [HD [HE [HR HT]]]]]]].
 assert (HZ:residual<>Z) by (exact (program230_difference_nonzero M x y residual HD Hxy)).
 destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
   (fun ax H rho => axioms M ax rho H) residual) as [H0|[z Hz]];[contradiction|].
 subst residual;rewrite inc_path_app_false in HE.
 destruct (equality_guard_unequal_history P parent loop guard wrapper reset Hguard M base z)
  as [f [g [HF HG]]].
 set (guardtime:=S (N 1+Program230ResetLoop.program230_reset_time M z)).
 assert (Hnz:guardtime<>Z) by
  (intro H;apply (zero_ne_succ M (N 1+Program230ResetLoop.program230_reset_time M z));symmetry;exact H).
 destruct (equality_test_pad_guard base pc (S z) f g guardtime
  (cfg base (program230_path_value M (brk 1 P)) Z Z) HE HF Hnz HG)
  as [r [s [HK HL]]].
 destruct (program230_history_join M p230_instruction_formula u v (program230_comparison_time M x)
   r s guardtime _ _ HR HT HK) as [j [k [HJ [Hpre Hpost]]]].
 set (time:=program230_comparison_time M x+guardtime).
 pose proof (proj1 (Hpost guardtime _ (coding_lt_succ M guardtime)) HL) as Hlast.
 assert (Hpos:coding_lt M Z time) by (apply equality_test_positive_sum).
 assert (Htime:time<>Z) by
  (intro H;rewrite H in Hpos;exact (coding_not_lt_zero M Z Hpos)).
 destruct (p230_history_ipeq_endpoint M j k time
   (cfg base (program230_path_value M (P++[false])) x y) (P++[false]) P
   (cfg base (program230_path_value M (brk 1 P)) Z Z)
   eq_refl (ipeq_app_false P) HJ Htime Hlast) as [p [q [HP [HQ _]]]].
 exists p,q,time;split;[|split;assumption].
 change (program230_history M p230_instruction_formula p q time
  (program230_with_pc (cfg base (program230_path_value M (P++[false])) x y)
    (program230_path_value M P)));exact HP.
Qed.
End EqualityTest.
Print Assumptions equality_test_equal_history.
Print Assumptions equality_test_unequal_history.
