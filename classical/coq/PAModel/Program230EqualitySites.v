(** Both outcomes of every actual equality-test occurrence. *)
From PAModel Require Import Model FiniteCoding Program230Configurations Program230Histories
 Program230InstructionFormula Program230PathCode Program230ComparisonIteration
 Program230ComparisonSites Program230ComparisonGuards Program230EqualityTest.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Inductive p230_equality_site:list bool->Prop :=
| equality_site_0:p230_equality_site p230_comparison_parent_path_0
| equality_site_1:p230_equality_site p230_comparison_parent_path_1
| equality_site_2:p230_equality_site p230_comparison_parent_path_2
| equality_site_3:p230_equality_site p230_comparison_parent_path_3.

Definition p230_equality_result M P base x y :=
 (x=y -> exists b c time,
  program230_history M p230_instruction_formula b c time
   (program230_comparison_state base (program230_path_value M P) x y) /\
  program230_state_at M b c time
   (program230_comparison_state base (program230_path_value M (inc_path P++[false])) (zeroM M) (zeroM M)) /\
  coding_lt M (zeroM M) time) /\
 (x<>y -> exists b c time,
  program230_history M p230_instruction_formula b c time
   (program230_comparison_state base (program230_path_value M P) x y) /\
  program230_state_at M b c time
   (program230_comparison_state base (program230_path_value M (brk 1 P)) (zeroM M) (zeroM M)) /\
  coding_lt M (zeroM M) time).

Lemma p230_equality_result_of_certificates M P base x y parent loop guard wrapper reset a b c d e:
 p230_comparison_guard_occurrence p230 P parent loop guard wrapper reset ->
 p230_comparison_occurrence p230 (P++[false]) loop a b c d e ->
 p230_equality_result M P base x y.
Proof.
 intros HG HL;split;intro H.
 -exact (equality_test_equal_history P parent loop guard wrapper reset a b c d e HG HL M base x y H).
 -exact (equality_test_unequal_history P parent loop guard wrapper reset a b c d e HG HL M base x y H).
Qed.

Theorem p230_equality_site_histories M P base x y:
 p230_equality_site P -> p230_equality_result M P base x y.
Proof.
 intro Hsite;destruct Hsite.
 -apply (p230_equality_result_of_certificates M p230_comparison_parent_path_0 base x y
   4953 4954 4960 4961 4962 4955 4956 4957 4958 4959).
  +exact p230_comparison_guard_site_0.
  +rewrite p230_comparison_parent_loop_0;exact p230_comparison_site_0.
 -apply (p230_equality_result_of_certificates M p230_comparison_parent_path_1 base x y
   4970 4971 4977 4978 4979 4972 4973 4974 4975 4976).
  +exact p230_comparison_guard_site_1.
  +rewrite p230_comparison_parent_loop_1;exact p230_comparison_site_1.
 -apply (p230_equality_result_of_certificates M p230_comparison_parent_path_2 base x y
   4984 4985 4991 4992 4993 4986 4987 4988 4989 4990).
  +exact p230_comparison_guard_site_2.
  +rewrite p230_comparison_parent_loop_2;exact p230_comparison_site_2.
 -apply (p230_equality_result_of_certificates M p230_comparison_parent_path_3 base x y
   5089 5090 5096 5097 5098 5091 5092 5093 5094 5095).
  +exact p230_comparison_guard_site_3.
  +rewrite p230_comparison_parent_loop_3;exact p230_comparison_site_3.
Qed.
Print Assumptions p230_equality_site_histories.
