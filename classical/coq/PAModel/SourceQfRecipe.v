(** Exact Qf K b recipe: Dn K (D0f b), then exchange source indices1,2. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions NumericalProofs
  NumericalEnvironments NumericalRenamingMaps NumericalRenaming SourceNumeralLift SourceRenamingBounds
  SourceBounded SetFormulaCodes SchemaRenamingDescriptors SourceD0Recipe SourceDn SourceDnBounds.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Lemma source_qf_exchange_zero M :
  renaming_lookup M (code_numeral M 210) (code_numeral M 6) (code_numeral M 3) (zeroM M)
    (zeroM M) (zeroM M).
Proof.
  apply (proj2 (renaming_lookup_inside M _ _ _ _ _ _ (coding_zero_lt_succ M (code_numeral M 2)))).
  apply (descriptor_beta_certificate M 210 6 0 0 30);reflexivity||lia.
Qed.
Lemma source_qf_exchange_one M :
  renaming_lookup M (code_numeral M 210) (code_numeral M 6) (code_numeral M 3) (zeroM M)
    (code_numeral M 1) (code_numeral M 2).
Proof.
  apply (proj2 (renaming_lookup_inside M _ _ _ _ _ _
    ((proj2 (coding_lt_succ_cancel M (zeroM M) (code_numeral M 2))) (coding_zero_lt_succ M (code_numeral M 1))))).
  apply (descriptor_beta_certificate M 210 6 1 2 16);reflexivity||lia.
Qed.
Lemma source_qf_exchange_two M :
  renaming_lookup M (code_numeral M 210) (code_numeral M 6) (code_numeral M 3) (zeroM M)
    (code_numeral M 2) (code_numeral M 1).
Proof.
  apply (proj2 (renaming_lookup_inside M _ _ _ _ _ _ (coding_lt_succ M (code_numeral M 2)))).
  apply (descriptor_beta_certificate M 210 6 2 1 11);reflexivity||lia.
Qed.
Lemma source_qf_exchange_outside M i : ~coding_lt M i (code_numeral M 3) ->
  renaming_lookup M (code_numeral M 210) (code_numeral M 6) (code_numeral M 3) (zeroM M) i i.
Proof. intro H. right. split;[exact H|]. symmetry. apply coding_add_zero_r. Qed.

Theorem source_qf_exchange_bounded M phi exchanged n :
  source_bounded M phi (succM M (succM M (succM M n))) ->
  numerical_renaming M phi (code_numeral M 210) (code_numeral M 6) (code_numeral M 3) (zeroM M) exchanged ->
  source_bounded M exchanged (succM M (succM M (succM M n))).
Proof.
  intros HF HR. apply (numerical_renaming_preserves_bound M phi _ _ _ _ exchanged _ _ HF HR).
  intros i j HI HJ. destruct (environment_lt_cases M i (code_numeral M 3)) as [HS|HS].
  - destruct (source_numeral_initial_segment M 3 i HS) as (v & HV & ->).
    destruct v as [|[|[|v]]];try lia.
    + assert (E : j = zeroM M) by (eapply renaming_lookup_functional;[exact HJ|apply source_qf_exchange_zero]).
      subst j. apply coding_zero_lt_succ.
    + assert (E : j = code_numeral M 2) by (eapply renaming_lookup_functional;[exact HJ|apply source_qf_exchange_one]).
      subst j. apply coding_lt_succ_cancel,coding_lt_succ_cancel,coding_zero_lt_succ.
    + assert (E : j = code_numeral M 1) by (eapply renaming_lookup_functional;[exact HJ|apply source_qf_exchange_two]).
      subst j. apply coding_lt_succ_cancel,coding_zero_lt_succ.
  - assert (E : j = i) by (eapply renaming_lookup_functional;[exact HJ|apply source_qf_exchange_outside;exact HS]).
    now subst j.
Qed.

Definition source_qf_recipe M domain level count body out := exists d0 dn,
  source_d0_recipe M domain level body d0 /\ source_dn M count d0 dn /\
  numerical_renaming M dn (code_numeral M 210) (code_numeral M 6) (code_numeral M 3) (zeroM M) out.
Definition source_qf_recipe_formula (domain level count body out:term) : form :=
  ∃∃ (source_d0_recipe_formula (code_lift2 domain) (code_lift2 level) (code_lift2 body) $1 ∧
    (source_dn_formula (code_lift2 count) $1 $0 ∧
    numerical_renaming_formula $0 (num 210) (num 6) (num 3) zero (code_lift2 out))).
Local Opaque holds source_d0_recipe_formula source_dn_formula numerical_renaming_formula.
Theorem source_qf_recipe_formula_correct M rho domain level count body out :
  holds M rho (source_qf_recipe_formula domain level count body out) <->
  source_qf_recipe M (evalM M rho domain) (evalM M rho level) (evalM M rho count)
    (evalM M rho body) (evalM M rho out).
Proof.
  unfold source_qf_recipe_formula,source_qf_recipe. repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite source_d0_recipe_formula_correct. setoid_rewrite source_dn_formula_correct.
  setoid_rewrite numerical_renaming_formula_correct. repeat setoid_rewrite code_eval_num.
  setoid_rewrite code_eval_lift2. reflexivity.
Qed.

Theorem source_qf_recipe_total M domain level count body : exists out,source_qf_recipe M domain level count body out.
Proof.
  destruct (source_d0_recipe_total M domain level body) as [d0 H0].
  destruct (source_dn_total M count d0) as [dn HD].
  destruct (numerical_renaming_total M dn (code_numeral M 210) (code_numeral M 6) (code_numeral M 3) (zeroM M)) as [out HR].
  exists out,d0,dn. auto.
Qed.

Lemma qf_add_succ_right M x y : addM M x (succM M y) = succM M (addM M x y).
Proof. rewrite Arithmetic.add_comm,Arithmetic.add_succ,Arithmetic.add_comm. reflexivity. Qed.

Theorem source_qf_recipe_bounded M domain level count body out n :
  source_bounded M domain (code_numeral M 1) -> source_bounded M level (code_numeral M 2) ->
  source_bounded M body (addM M count (succM M (succM M n))) ->
  source_qf_recipe M domain level count body out -> source_bounded M out (succM M (succM M (succM M n))).
Proof.
  intros HD HL HB (d0 & dn & H0 & HN & HR).
  apply (source_qf_exchange_bounded M dn out n);[|exact HR].
  apply (source_dn_bounded M count d0 dn (succM M n) HN).
  assert (HB' : source_bounded M body (succM M (addM M count (succM M n)))).
  { rewrite <-qf_add_succ_right. exact HB. }
  pose proof (source_d0_recipe_bounded M domain level body d0 (addM M count (succM M n)) HD HL HB' H0) as H.
  rewrite <-qf_add_succ_right,<-qf_add_succ_right in H. exact H.
Qed.

Print Assumptions source_qf_exchange_bounded.
Print Assumptions source_qf_recipe_formula_correct.
Print Assumptions source_qf_recipe_total.
Print Assumptions source_qf_recipe_bounded.
