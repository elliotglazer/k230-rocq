(** An ordinary PA formula for the whole dispatcher simulation state.
    The register arguments are its actual nine logical scalar fields. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
 TM230BinaryStep TM230BitArithmetic TM230SpareSyntax TM230RegisterWords
 TM230RuntimeBox TM230PhysicalRegisters TM230P230Control TM230DispatchCode TM230SimulationState.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
Definition machine230_plain_box_formula(regs:nat->term)(E word:term):form:=
 Peano.sless zero E ∧∃(machine230_spare_formula E`[↑] $0 ∧
  machine230_register_file_formula(fun idx =>(regs idx)`[↑])$0 word`[↑]).
Local Opaque holds Peano.sless machine230_spare_formula machine230_register_file_formula.
Theorem machine230_plain_box_formula_correct M rho regs E word:
 holds M rho(machine230_plain_box_formula regs E word)<->
 machine230_runtime_box M(machine230_physical_values M(fun idx =>evalM M rho(regs idx)))
  (evalM M rho E)(Runtime230.BPlain Runtime230.FNone)(evalM M rho word).
Proof.
 unfold machine230_plain_box_formula;rewrite holds_and,less_formula_correct,holds_ex.
 setoid_rewrite holds_and. setoid_rewrite machine230_spare_formula_correct.
 setoid_rewrite machine230_register_file_formula_correct.
 repeat setoid_rewrite register_eval_up.
 split.
 -intros[HE[spare[HS HF]]]. rewrite(register_eval_up M rho spare E)in HS.
  rewrite(register_eval_up M rho spare word)in HF. apply(machine230_register_box_intro M(fun idx =>evalM M rho(regs idx))
   (evalM M rho E)spare(evalM M rho word)HE HS).
  unfold machine230_register_file in HF|-*.
  apply(proj1(machine230_blocks_ext M 9
   (fun idx =>evalM M(spare.:rho)(regs(machine230_physical_register idx))`[↑])
   (fun idx =>evalM M rho(regs(machine230_physical_register idx)))spare(evalM M rho word)
   ltac:(intro i;apply register_eval_up)));exact HF.
 -intros[HL[HE[updated[spare[HU[HS HW]]]]]].
  change(updated=machine230_physical_values M(fun idx =>evalM M rho(regs idx)))in HU;subst updated.
  split;[exact HE|]. exists spare;split;[now rewrite register_eval_up|].
  rewrite(register_eval_up M rho spare word).
  apply(proj1(machine230_register_file_list M(fun idx =>evalM M rho(regs idx))spare(evalM M rho word)))in HW.
  unfold machine230_register_file in HW|-*.
  apply(proj2(machine230_blocks_ext M 9
   (fun idx =>evalM M(spare.:rho)(regs(machine230_physical_register idx))`[↑])
   (fun idx =>evalM M rho(regs(machine230_physical_register idx)))spare(evalM M rho word)
   ltac:(intro i;apply register_eval_up)));exact HW.
Qed.
Definition machine230_simulation_lift5(t:term):=t`[↑]`[↑]`[↑]`[↑]`[↑].
Lemma machine230_simulation_lift5_eval M rho a b c d e t:
 evalM M(e.:d.:c.:b.:a.:rho)(machine230_simulation_lift5 t)=evalM M rho t.
Proof. unfold machine230_simulation_lift5;repeat rewrite register_eval_up;reflexivity. Qed.
Definition machine230_simulation_formula(pc:term)(regs:nat->term)(state left head right:term):form:=
 ∃∃∃∃∃(machine230_p230_control_formula $4(machine230_simulation_lift5 pc) ∧
 (machine230_plain_box_formula(fun idx =>machine230_simulation_lift5(regs idx))$1 $0 ∧
 (machine230_dispatch_code_formula(machine230_simulation_lift5 pc)$4 $3 $0
  (machine230_simulation_lift5 state)(machine230_simulation_lift5 left)
  (machine230_simulation_lift5 head)(machine230_simulation_lift5 right) ∧
  $4⊕$3==$2⊕num 64))).
Local Opaque machine230_plain_box_formula machine230_p230_control_formula machine230_dispatch_code_formula.
Theorem machine230_simulation_formula_correct M rho pc regs state left head right:
 holds M rho(machine230_simulation_formula pc regs state left head right)<->
 machine230_simulation_state M(evalM M rho pc)(fun idx =>evalM M rho(regs idx))
  (machine230_mk_config(carrier M)(evalM M rho state)(evalM M rho left)(evalM M rho head)(evalM M rho right)).
Proof.
 assert(HB:forall a b c d e,
  holds M(e.:d.:c.:b.:a.:rho)(machine230_plain_box_formula(fun idx =>machine230_simulation_lift5(regs idx))$1 $0)<->
  machine230_runtime_box M(machine230_physical_values M(fun idx =>evalM M rho(regs idx)))d(Runtime230.BPlain Runtime230.FNone)e).
 {intros a b c d e. rewrite machine230_plain_box_formula_correct.
  assert(ER:machine230_physical_values M(fun idx =>evalM M(e.:d.:c.:b.:a.:rho)(machine230_simulation_lift5(regs idx)))=
   machine230_physical_values M(fun idx =>evalM M rho(regs idx))).
  {apply machine230_physical_list_ext;intros i Hi;apply machine230_simulation_lift5_eval. }
  rewrite ER;reflexivity. }
 unfold machine230_simulation_formula,machine230_simulation_state.
 repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
 setoid_rewrite HB. setoid_rewrite machine230_p230_control_formula_correct.
 setoid_rewrite machine230_dispatch_code_formula_correct. setoid_rewrite machine230_holds_equal.
 repeat setoid_rewrite machine230_eval_add. repeat setoid_rewrite machine230_simulation_lift5_eval.
 repeat setoid_rewrite code_eval_num. reflexivity.
Qed.
Print Assumptions machine230_plain_box_formula_correct.
Print Assumptions machine230_simulation_formula_correct.
