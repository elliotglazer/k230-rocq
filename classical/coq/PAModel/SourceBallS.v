(** A genuine PA-definable graph for ballS, with arbitrary internal count,
    carrier name and matrix. Its rules compute syntax only. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  SetFormulaCodes NumericalTraces SourceBallSRules NumericalSubstitutionMaps.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_ballS M n y body out:=exists r,
  balls_record M n y body out r /\trace_derives M source_balls_rules r.
Definition source_ballS_formula(n y body out:term):form:=∃(
  balls_record_formula n`[↑] y`[↑] body`[↑] out`[↑] $0 ∧trace_derives_formula source_balls_rules $0).
Local Opaque holds balls_record_formula trace_derives_formula.
Theorem source_ballS_formula_correct M rho n y body out:
  holds M rho(source_ballS_formula n y body out)<->
  source_ballS M(evalM M rho n)(evalM M rho y)(evalM M rho body)(evalM M rho out).
Proof.
  unfold source_ballS_formula,source_ballS. setoid_rewrite holds_ex.
  setoid_rewrite holds_and. setoid_rewrite balls_record_formula_correct.
  setoid_rewrite trace_derives_formula_correct. unfold evalM. now setoid_rewrite eval_up.
Qed.
Theorem source_ballS_zero_intro M y body:source_ballS M(zeroM M)y body body.
Proof.
  destruct(balls_record_total M(zeroM M)y body body)as(r&HR).
  exists r. split;[exact HR|]. apply trace_derives_base,balls_rule_base. exists y,body. exact HR.
Qed.
Theorem source_ballS_step_intro M n y body previous out:
  source_ballS M n(succM M y)body previous ->balls_step M y previous out ->
  source_ballS M(succM M n)y body out.
Proof.
  intros(p&HP&PD)HO. destruct(balls_record_total M(succM M n)y body out)as(r&HR).
  exists r. split;[exact HR|]. apply(trace_derives_unary M source_balls_rules r p PD),balls_rule_unary.
  exists n,y,body,out,previous. auto.
Qed.
Lemma source_ballS_total_definable M:Definable1 M(fun n=>forall y body,exists out,source_ballS M n y body out).
Proof.
  exists(∀∀∃source_ballS_formula $3 $2 $1 $0),(fun _=>zeroM M). intro n.
  repeat setoid_rewrite holds_all. setoid_rewrite holds_ex.
  setoid_rewrite source_ballS_formula_correct. reflexivity.
Qed.
Theorem source_ballS_total M n y body:exists out,source_ballS M n y body out.
Proof.
  revert n y body. apply(definable_induction M _ (source_ballS_total_definable M)).
  - intros y body. exists body. apply source_ballS_zero_intro.
  - intros n IH y body. destruct(IH(succM M y)body)as(previous&HP).
    destruct(balls_step_total M y previous)as(out&HO). exists out.
    exact(source_ballS_step_intro M n y body previous out HP HO).
Qed.
Theorem source_ballS_cases M n y body out:source_ballS M n y body out ->
  (n=zeroM M /\out=body) \/
  exists k previous,n=succM M k /\source_ballS M k(succM M y)body previous /\balls_step M y previous out.
Proof.
  intros(r&HR&HD). destruct(trace_derives_inv M source_balls_rules r HD)
    as[HB|[(p&HP&HU)|(p&q&HP&HQ&HB)]].
  - apply balls_rule_base in HB. destruct HB as(y'&body'&HR').
    destruct(balls_record_injective M n y body out(zeroM M)y' body' body' r HR HR')as(En&Ey&Eb&Eo).
    left. split;[exact En|congruence].
  - apply balls_rule_unary in HU. destruct HU as(k&y'&body'&out'&previous&HR'&HChild&HStep).
    destruct(balls_record_injective M n y body out(succM M k)y' body' out' r HR HR')as(En&Ey&Eb&Eo).
    subst y' body' out'. right. exists k,previous. split;[exact En|]. split;[exists p;auto|exact HStep].
  - exfalso. exact(proj1(substitution_holds_false M(r .:p .:q .:fun _=>zeroM M))HB).
Qed.
Theorem source_ballS_zero M y body out:source_ballS M(zeroM M)y body out<->out=body.
Proof.
  split.
  - intro H. destruct(source_ballS_cases M(zeroM M)y body out H)as[[_ E]|(k&p&E&_)];[exact E|].
    exfalso. exact(zero_ne_succ M k E).
  - intros ->. apply source_ballS_zero_intro.
Qed.
Theorem source_ballS_succ M n y body out:source_ballS M(succM M n)y body out<->
  exists previous,source_ballS M n(succM M y)body previous /\balls_step M y previous out.
Proof.
  split.
  - intro H. destruct(source_ballS_cases M(succM M n)y body out H)as[(E&_)|(k&p&E&HP&HO)].
    + exfalso. exact(zero_ne_succ M n(eq_sym E)).
    + apply succ_injective in E. subst k. exists p. auto.
  - intros(p&HP&HO). exact(source_ballS_step_intro M n y body p out HP HO).
Qed.
Definition balls_functional_at M n:=forall y body out out',
  source_ballS M n y body out ->source_ballS M n y body out' ->out=out'.
Lemma balls_functional_definable M:Definable1 M(balls_functional_at M).
Proof.
  exists(∀∀∀∀(source_ballS_formula $4 $3 $2 $1 →source_ballS_formula $4 $3 $2 $0 →$1==$0)),
    (fun _=>zeroM M). intro n. unfold balls_functional_at.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite source_ballS_formula_correct. reflexivity.
Qed.
Theorem source_ballS_functional M n:balls_functional_at M n.
Proof.
  revert n. apply(definable_induction M _ (balls_functional_definable M)).
  - intros y body out out' HO HO'. apply source_ballS_zero in HO,HO'. congruence.
  - intros n IH y body out out' HO HO'. apply source_ballS_succ in HO,HO'.
    destruct HO as(p&HP&HS),HO' as(p'&HP'&HS').
    pose proof(IH(succM M y)body p p' HP HP')as E. subst p'.
    exact(balls_step_functional M y p out out' HS HS').
Qed.
Print Assumptions source_ballS_formula_correct.
Print Assumptions source_ballS_total.
Print Assumptions source_ballS_functional.
Print Assumptions source_ballS_succ.


