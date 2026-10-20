(** Uniform induction for the destructive comparison loop. The three finite
    control contracts below remain explicit until instantiated at actual sites. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
 Program230ComparisonArithmetic Program230Configurations Program230Histories
 Program230HistoryJoin Program230InstructionFormula Program230PathCode.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import Lists.List Arith.Arith Lia setoid_ring.Ring.
Import ListNotations.
Unset Implicit Arguments.

Definition program230_comparison_state {D}(base:program230_configuration D) pc x y :=
 mkProgram230Configuration D pc (program230_r0 base) (program230_r1 base)
  (program230_r2 base) (program230_r3 base) (program230_r4 base) y x
  (program230_r7 base) (program230_r8 base).
Definition program230_comparison_time M x :=
 addM M (mulM M (code_numeral M 3) x) (code_numeral M 1).
Definition program230_comparison_time_term x:term := (num 3⊗x)⊕num 1.
Definition program230_comparison_exit M exit pc :=
 pc=program230_path_value M exit \/ pc=program230_path_value M (exit++[false;false;false]).
Definition program230_comparison_exit_formula exit pc:form :=
 (pc==program230_path_term exit) ∨ (pc==program230_path_term (exit++[false;false;false])).

Lemma program230_comparison_eval M rho base pc x y:
 program230_eval_config M rho (program230_comparison_state base pc x y)=
 program230_comparison_state (program230_eval_config M rho base)
  (evalM M rho pc) (evalM M rho x) (evalM M rho y).
Proof. destruct base;reflexivity. Qed.
Lemma program230_comparison_time_correct M rho x:
 evalM M rho (program230_comparison_time_term x)=program230_comparison_time M (evalM M rho x).
Proof.
 unfold program230_comparison_time_term,program230_comparison_time.
 change (addM M (mulM M (evalM M rho (num 3)) (evalM M rho x)) (evalM M rho (num 1))=
  addM M (mulM M (code_numeral M 3) (evalM M rho x)) (code_numeral M 1)).
 now rewrite !code_eval_num.
Qed.
Lemma program230_comparison_exit_correct M rho exit pc:
 holds M rho (program230_comparison_exit_formula exit pc)<->program230_comparison_exit M exit (evalM M rho pc).
Proof.
 unfold program230_comparison_exit_formula,program230_comparison_exit.
 rewrite holds_or.
 change ((evalM M rho pc=evalM M rho (program230_path_term exit) \/
 evalM M rho pc=evalM M rho (program230_path_term (exit++[false;false;false])))<->
 (evalM M rho pc=program230_path_value M exit \/
 evalM M rho pc=program230_path_value M (exit++[false;false;false]))).
 now rewrite !program230_path_term_correct.
Qed.

Definition program230_comparison_cycle M P := forall base x y,
 exists b c,program230_history M p230_instruction_formula b c (code_numeral M 3)
  (program230_comparison_state base (program230_path_value M P) (succM M x) (succM M y)) /\
 program230_state_at M b c (code_numeral M 3)
  (program230_comparison_state base (program230_path_value M P) x y).
Definition program230_comparison_zero_exit M P exit := forall base y,
 exists b c,program230_history M p230_instruction_formula b c (code_numeral M 1)
  (program230_comparison_state base (program230_path_value M P) (zeroM M) y) /\
 program230_state_at M b c (code_numeral M 1)
  (program230_comparison_state base (program230_path_value M exit) (zeroM M) y).
Definition program230_comparison_leftover_exit M P exit := forall base x,
 exists b c,program230_history M p230_instruction_formula b c (program230_comparison_time M (succM M x))
  (program230_comparison_state base (program230_path_value M P) (succM M x) (zeroM M)) /\
 program230_state_at M b c (program230_comparison_time M (succM M x))
  (program230_comparison_state base (program230_path_value M (exit++[false;false;false])) (zeroM M) (succM M x)).

Definition program230_comparison_property M P exit base x := forall y,
 exists residual pc b c,program230_difference M x y residual /\
 program230_comparison_exit M exit pc /\
 program230_history M p230_instruction_formula b c (program230_comparison_time M x)
  (program230_comparison_state base (program230_path_value M P) x y) /\
 program230_state_at M b c (program230_comparison_time M x)
  (program230_comparison_state base pc (zeroM M) residual).
Definition program230_comparison_parameters := program230_config_of (fun j => $(6+j)).
Definition program230_comparison_property_formula P exit:form := ∀∃∃∃∃
 (program230_difference_formula $5 $4 $3 ∧
 (program230_comparison_exit_formula exit $2 ∧
 (program230_history_formula p230_instruction_formula $1 $0 (program230_comparison_time_term $5)
  (program230_comparison_state program230_comparison_parameters (program230_path_term P) $5 $4) ∧
 program230_state_at_formula $1 $0 (program230_comparison_time_term $5)
  (program230_comparison_state program230_comparison_parameters $2 zero $3)))).
Lemma program230_comparison_parameters_eval M base x y residual pc b c:
 program230_eval_config M (c.:b.:pc.:residual.:y.:x.:program230_field base)
  program230_comparison_parameters=base.
Proof.
 apply p230_configuration_ext;intros j Hj;rewrite program230_eval_field by exact Hj.
 unfold program230_comparison_parameters;rewrite program230_config_of_fields by exact Hj;reflexivity.
Qed.
Local Opaque holds program230_history_formula program230_state_at_formula
 program230_difference_formula program230_comparison_exit_formula.
Lemma program230_comparison_definable M P exit base:
 Definable1 M (program230_comparison_property M P exit base).
Proof.
 exists (program230_comparison_property_formula P exit),(program230_field base);intro x.
 unfold program230_comparison_property_formula,program230_comparison_property.
 repeat setoid_rewrite holds_all;repeat setoid_rewrite holds_ex;repeat setoid_rewrite holds_and.
 setoid_rewrite program230_difference_formula_correct.
 setoid_rewrite program230_comparison_exit_correct.
 setoid_rewrite program230_history_formula_correct;setoid_rewrite program230_state_at_formula_correct.
 setoid_rewrite program230_comparison_eval;setoid_rewrite program230_comparison_parameters_eval.
 setoid_rewrite program230_comparison_time_correct;setoid_rewrite program230_path_term_correct.
 reflexivity.
Qed.

Section Induction.
Variable M:Model.
Local Notation Z := (zeroM M).
Local Notation S := (succM M).
Local Infix "+" := (addM M).
Local Infix "*" := (mulM M).
Add Ring comparison_iteration_ring : (model_semiring M).
Lemma program230_comparison_time_zero:program230_comparison_time M Z=code_numeral M 1.
Proof. unfold program230_comparison_time;ring. Qed.
Lemma program230_comparison_time_step x:
 program230_comparison_time M (S x)=code_numeral M 3+program230_comparison_time M x.
Proof. unfold program230_comparison_time;rewrite (succ_as_add M x);cbn [code_numeral];ring. Qed.
Theorem program230_comparison_induction P exit:
 program230_comparison_cycle M P -> program230_comparison_zero_exit M P exit ->
 program230_comparison_leftover_exit M P exit ->
 forall base x,program230_comparison_property M P exit base x.
Proof.
 intros HC HZ HL base.
 apply (definable_induction M (program230_comparison_property M P exit base)
  (program230_comparison_definable M P exit base)).
 -intro y;destruct (HZ base y) as [b [c [HR HT]]].
  exists y,(program230_path_value M exit),b,c;split;[apply program230_difference_left_zero|].
  split;[left;reflexivity|]. rewrite program230_comparison_time_zero;auto.
 -intros x IH y.
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
   (fun ax H rho => axioms M ax rho H) y) as [Hy|[z Hy]].
  +subst y;destruct (HL base x) as [b [c [HR HT]]].
   exists (S x),(program230_path_value M (exit++[false;false;false])),b,c.
   split;[apply program230_difference_right_zero|]. split;[right;reflexivity|auto].
  +subst y;destruct (HC base x z) as [b [c [HR HT]]].
   destruct (IH z) as [residual [pc [d [e [HD [HE [HU HV]]]]]]].
   destruct (program230_history_join M p230_instruction_formula b c (code_numeral M 3)
     d e (program230_comparison_time M x) _ _ HR HT HU) as [f [g [HG [Hpre Hpost]]]].
   exists residual,pc,f,g;split;[apply program230_difference_successors;exact HD|].
   split;[exact HE|]. rewrite program230_comparison_time_step;split;[exact HG|].
   exact (proj1 (Hpost (program230_comparison_time M x) _
    (coding_lt_succ M (program230_comparison_time M x))) HV).
Qed.
End Induction.
Print Assumptions program230_comparison_definable.
Print Assumptions program230_comparison_induction.
