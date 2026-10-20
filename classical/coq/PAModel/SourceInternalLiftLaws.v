(** Literal laws for internal-depth lifted substitution maps. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT FiniteCRTFormula
  CodeExpressions NumericalProofs NumericalEnvironments NumericalSubstitutionMaps SourceInternalLifts.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.
Lemma internal_add_succ_right M h x:addM M h(succM M x)=succM M(addM M h x).
Proof. rewrite coding_add_comm,Arithmetic.add_succ,coding_add_comm. reflexivity. Qed.
Definition source_upn_map_formula(h b c n base db dc:term):form:=∀∀(
  (substitution_lookup_formula(code_lift2 db)(code_lift2 dc)(code_lift2 h⊕code_lift2 n)
    (code_lift2 h⊕code_lift2 base)$1 $0 →
    source_upn_index_formula(code_lift2 h)(code_lift2 b)(code_lift2 c)(code_lift2 n)(code_lift2 base)$1 $0) ∧
  (source_upn_index_formula(code_lift2 h)(code_lift2 b)(code_lift2 c)(code_lift2 n)(code_lift2 base)$1 $0 →
    substitution_lookup_formula(code_lift2 db)(code_lift2 dc)(code_lift2 h⊕code_lift2 n)
    (code_lift2 h⊕code_lift2 base)$1 $0)).
Local Opaque holds substitution_lookup_formula source_upn_index_formula.
Theorem source_upn_map_formula_correct M rho h b c n base db dc:
  holds M rho(source_upn_map_formula h b c n base db dc)<->
  source_upn_map M(evalM M rho h)(evalM M rho b)(evalM M rho c)(evalM M rho n)
    (evalM M rho base)(evalM M rho db)(evalM M rho dc).
Proof.
  unfold source_upn_map_formula,source_upn_map. repeat setoid_rewrite holds_all.
  setoid_rewrite holds_and. repeat setoid_rewrite holds_imp.
  setoid_rewrite substitution_lookup_formula_correct. setoid_rewrite source_upn_index_formula_correct.
  setoid_rewrite substitution_eval_add. repeat setoid_rewrite code_eval_lift2.
  split;intros H i v;exact(H i v).
Qed.
Theorem source_upn_index_zero M b c n base i v:
  source_upn_index M(zeroM M)b c n base i v<->substitution_lookup M b c n base i v.
Proof.
  split.
  - intros[(HI&_)|(_&j&w&HI&HW&HV)].
    + exfalso. exact(coding_not_lt_zero M i HI).
    + rewrite coding_add_zero in HI,HV. now subst i v.
  - intro HV. right. split;[apply coding_not_lt_zero|]. exists i,v. now rewrite!coding_add_zero.
Qed.
Theorem source_upn_map_zero M b c n base db dc:
  source_upn_map M(zeroM M)b c n base db dc ->
  substitution_equivalent M db dc n b c n base.
Proof.
  intros HM i v. unfold source_upn_map in HM. specialize(HM i v).
  rewrite!coding_add_zero in HM. now rewrite source_upn_index_zero in HM.
Qed.
Theorem source_upn_index_succ M h b c n base i v:
  source_upn_index M h b c n base i v ->
  source_upn_index M(succM M h)b c n base(succM M i)(succM M v).
Proof.
  intros[(HI&->)|(HI&j&w&HE&HW&HV)].
  - left. split;[exact(proj2(coding_lt_succ_cancel M i h)HI)|reflexivity].
  - right. split.
    + intro H. apply HI. exact(proj1(coding_lt_succ_cancel M i h)H).
    + exists j,w. rewrite!Arithmetic.add_succ. repeat split;congruence.
Qed.
Theorem source_upn_map_successor_lift M h b c n base db dc ub uc:
  source_upn_map M h b c n base db dc ->source_upn_map M(succM M h)b c n base ub uc ->
  substitution_lift M db dc(addM M h n)(addM M h base)ub uc(addM M(succM M h)n).
Proof.
  intros HM HN. split;[apply Arithmetic.add_succ|]. split.
  - rewrite<-Arithmetic.add_succ. exact(source_upn_map_head M(succM M h)b c n base ub uc(zeroM M)HN(coding_zero_lt_succ M h)).
  - intros i v HI. rewrite<-Arithmetic.add_succ. apply HN.
    exact(source_upn_index_succ M h b c n base i v(proj1(HM i v)HI)).
Qed.
Theorem source_upn_index_after_lift M h b c n base lb lc ln i v:
  substitution_lift M b c n base lb lc ln ->
  source_upn_index M h lb lc ln(succM M base)i v ->
  source_upn_index M(succM M h)b c n base i v.
Proof.
  intros HL[(HI&->)|(HI&j&w&HE&HW&HV)].
  - left. split;[apply coding_lt_succ_cases;now left|reflexivity].
  - destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)j)
      as[E|(q&E)];subst j.
    + pose proof(proj1(substitution_lift_head M b c n base lb lc ln w HL)HW)as EW. subst w.
      rewrite coding_add_zero_r in HE,HV. subst i v. left. split;[apply coding_lt_succ|reflexivity].
    + destruct(substitution_lift_tail_inv M b c n base lb lc ln q w HL HW)as(z&HZ&EW). subst w.
      change(i = addM M h(succM M q))in HE.
      rewrite!internal_add_succ_right in HE,HV.
      right. split.
      * rewrite HE. rewrite<-Arithmetic.add_succ. apply source_upn_not_lt_add.
      * exists q,z. rewrite!Arithmetic.add_succ. auto.
Qed.
Theorem source_upn_map_after_lift M h b c n base lb lc ln ub uc:
  substitution_lift M b c n base lb lc ln ->source_upn_map M h lb lc ln(succM M base)ub uc ->
  source_upn_map M(succM M h)b c n base ub uc.
Proof.
  intros HL HM. assert(Elen:addM M h ln=addM M(succM M h)n).
  { destruct HL as[-> _]. rewrite internal_add_succ_right,Arithmetic.add_succ. reflexivity. }
  assert(Ebase:addM M h(succM M base)=addM M(succM M h)base).
  { rewrite internal_add_succ_right,Arithmetic.add_succ. reflexivity. }
  intros i v. rewrite<-Elen,<-Ebase. split.
  - intro HV. apply(proj1(HM i v))in HV. exact(source_upn_index_after_lift M h b c n base lb lc ln i v HL HV).
  - intro HV. destruct(source_upn_index_total M h lb lc ln(succM M base)i)as(w&HW).
    pose proof(source_upn_index_functional M(succM M h)b c n base i v w HV
      (source_upn_index_after_lift M h b c n base lb lc ln i w HL HW))as E. subst w. now apply HM.
Qed.
Print Assumptions source_upn_map_formula_correct.
Print Assumptions source_upn_map_zero.
Print Assumptions source_upn_map_successor_lift.
Print Assumptions source_upn_map_after_lift.


