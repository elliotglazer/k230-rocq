(** Arbitrarily deep binder lifting of a numerical variable substitution.
    The depth is a PA-model value. Bounded collection and beta packing
    construct the actual finite prefix, rather than assuming an upn map. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT FiniteCRTFormula BetaPacking
  CodeExpressions NumericalProofs NumericalEnvironments NumericalSubstitutionMaps
  SourceBoundedMapComposition ProofClosure.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_upn_index M h b c n base i v:=
  (coding_lt M i h /\v = i) \/(~coding_lt M i h /\exists j w,
    i = addM M h j /\substitution_lookup M b c n base j w /\v = addM M h w).
Definition source_upn_index_formula(h b c n base i v:term):form:=
  (Peano.sless i h ∧v == i)∨((Peano.sless i h→⊥)∧∃∃(
    code_lift2 i == code_lift2 h ⊕ $1 ∧
    substitution_lookup_formula(code_lift2 b)(code_lift2 c)(code_lift2 n)(code_lift2 base)$1 $0 ∧
    code_lift2 v == code_lift2 h ⊕ $0)).
Local Opaque holds Peano.sless substitution_lookup_formula.
Theorem source_upn_index_formula_correct M rho h b c n base i v:
  holds M rho(source_upn_index_formula h b c n base i v)<->
  source_upn_index M(evalM M rho h)(evalM M rho b)(evalM M rho c)(evalM M rho n)
    (evalM M rho base)(evalM M rho i)(evalM M rho v).
Proof.
  unfold source_upn_index_formula,source_upn_index.
  repeat setoid_rewrite holds_or. repeat setoid_rewrite holds_and.
  repeat setoid_rewrite holds_imp. repeat setoid_rewrite holds_ex.
  repeat setoid_rewrite holds_and. setoid_rewrite less_formula_correct.
  setoid_rewrite substitution_holds_false. setoid_rewrite substitution_holds_eq.
  setoid_rewrite substitution_lookup_formula_correct. setoid_rewrite substitution_eval_add.
  repeat setoid_rewrite code_eval_lift2.
  split;intros[H|[H(j&w&T)]].
  - now left.
  - right. split;[exact H|]. exists j,w. tauto.
  - now left.
  - right. split;[exact H|]. exists j,w. tauto.
Qed.
Theorem source_upn_index_total M h b c n base i:exists v,source_upn_index M h b c n base i v.
Proof.
  destruct(environment_lt_cases M i h)as[HI|HI].
  - exists i. now left.
  - destruct(coding_difference M i h HI)as(j&HE).
    destruct(substitution_lookup_total M b c n base j)as(w&HW).
    exists(addM M h w). right. split;[exact HI|]. exists j,w. auto.
Qed.
Theorem source_upn_index_functional M h b c n base i v v':
  source_upn_index M h b c n base i v ->source_upn_index M h b c n base i v' ->v = v'.
Proof.
  intros[(H&->)|(H&j&w&HI&HW&->)][(H'&->)|(H'&j'&w'&HI'&HW'&->)];try contradiction;try reflexivity.
  assert(E:j=j').
  { apply(Arithmetic.add_cancel M j j' h). rewrite!(coding_add_comm M _ h). congruence. }
  subst j'. pose proof(substitution_lookup_functional M b c n base j w w' HW HW')as E. now subst w'.
Qed.
Lemma source_upn_not_lt_add M h j:~coding_lt M(addM M h j)h.
Proof.
  intro H. apply(coding_not_lt_zero M j). apply(lt_add_cancel M h j(zeroM M)).
  now rewrite coding_add_zero_r.
Qed.

Definition source_upn_map M h b c n base db dc:=forall i v,
  substitution_lookup M db dc(addM M h n)(addM M h base)i v<->source_upn_index M h b c n base i v.
Theorem source_upn_map_total M h b c n base:exists db dc,source_upn_map M h b c n base db dc.
Proof.
  set(rho:=h .:b .:c .:n .:base .:fun _=>zeroM M).
  set(F:=source_upn_index_formula $2 $3 $4 $5 $6 $1 $0).
  assert(HF:forall i v,holds M(v .:i .:rho)F<->source_upn_index M h b c n base i v).
  { intros i v. unfold F,rho. apply source_upn_index_formula_correct. }
  assert(HT:forall i,coding_lt M i(addM M h n)->exists v,holds M(v .:i .:rho)F).
  { intros i _. destruct(source_upn_index_total M h b c n base i)as(v&HV). exists v. now apply HF. }
  assert(HU:forall i v w,coding_lt M i(addM M h n)->holds M(v .:i .:rho)F->holds M(w .:i .:rho)F->v=w).
  { intros i v w _ HV HW. apply HF in HV,HW. exact(source_upn_index_functional M h b c n base i v w HV HW). }
  destruct(beta_pack_total_function M rho F(addM M h n)HT HU)as(db&dc&HBC).
  assert(HForward:forall i v,substitution_lookup M db dc(addM M h n)(addM M h base)i v->
    source_upn_index M h b c n base i v).
  { intros i v[(HI&HV)|(HI&q&HE&EV)].
    - apply HF. exact(proj1(HBC i v HI)HV).
    - assert(HIH:~coding_lt M i h).
      { intro H. exact(HI(lt_left_sum M i h n H)). }
      right. split;[exact HIH|]. exists(addM M n q),(addM M base q). split.
      + rewrite Arithmetic.add_assoc. exact HE.
      + split.
        * apply substitution_lookup_outside;[apply source_upn_not_lt_add|]. exists q. auto.
        * rewrite Arithmetic.add_assoc. exact EV. }
  exists db,dc. intros i v. split;[apply HForward|]. intro HV.
  destruct(substitution_lookup_total M db dc(addM M h n)(addM M h base)i)as(w&HW).
  pose proof(source_upn_index_functional M h b c n base i v w HV(HForward i w HW))as E.
  now subst w.
Qed.
Theorem source_upn_map_head M h b c n base db dc i:
  source_upn_map M h b c n base db dc ->coding_lt M i h ->
  substitution_lookup M db dc(addM M h n)(addM M h base)i i.
Proof. intros HM HI. apply HM. now left. Qed.
Theorem source_upn_map_tail M h b c n base db dc i v:
  source_upn_map M h b c n base db dc ->substitution_lookup M b c n base i v ->
  substitution_lookup M db dc(addM M h n)(addM M h base)(addM M h i)(addM M h v).
Proof.
  intros HM HV. apply HM. right. split;[apply source_upn_not_lt_add|]. exists i,v. auto.
Qed.
Print Assumptions source_upn_index_formula_correct.
Print Assumptions source_upn_map_total.
Print Assumptions source_upn_map_tail.


