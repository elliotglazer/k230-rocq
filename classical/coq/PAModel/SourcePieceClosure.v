(** Pc(K,b,d,X): the Dn witness-closure formula with only its ordinal and
    container roles reopened. For a genuine piece, every tail role is unused. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SourceBounded
  NumericalProofs NumericalRenaming NumericalSubstitutionMaps NumericalSubstitution SourceSubstitutionBounds
  SourceD0Recipe SourceQfFunctionality SourceDn SourceDnBounds SourceRoleReopening SourceNumeralLift.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_pc_instance M domain level count phi d X out:=exists d0 dn b c,
  source_d0_recipe M domain level phi d0 /\source_dn M count d0 dn /\
  source_role_reopening M X d b c /\numerical_substitution M dn b c(code_numeral M 2)(code_numeral M 2)out.
Definition pc_lift4(t:term):=t`[↑]`[↑]`[↑]`[↑].
Definition source_pc_instance_formula(domain level count phi d X out:term):form:=
  ∃∃∃∃(source_d0_recipe_formula(pc_lift4 domain)(pc_lift4 level)(pc_lift4 phi)$3 ∧
    (source_dn_formula(pc_lift4 count)$3 $2 ∧
    ((substitution_lookup_formula $1 $0(num 2)zero zero(pc_lift4 d) ∧
      substitution_lookup_formula $1 $0(num 2)zero(num 1)(pc_lift4 X)) ∧
      numerical_substitution_formula $2 $1 $0(num 2)(num 2)(pc_lift4 out)))).
Lemma pc_eval_lift4 M rho a b c d t:evalM M(a.:b.:c.:d.:rho)(pc_lift4 t)=evalM M rho t.
Proof. unfold pc_lift4,evalM. now rewrite !eval_up. Qed.
Local Opaque holds source_d0_recipe_formula source_dn_formula substitution_lookup_formula numerical_substitution_formula.

Theorem source_pc_instance_formula_correct M rho domain level count phi d X out:
  holds M rho(source_pc_instance_formula domain level count phi d X out) <->
  source_pc_instance M(evalM M rho domain)(evalM M rho level)(evalM M rho count)(evalM M rho phi)
    (evalM M rho d)(evalM M rho X)(evalM M rho out).
Proof.
  unfold source_pc_instance_formula,source_pc_instance,source_role_reopening.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite source_d0_recipe_formula_correct. setoid_rewrite source_dn_formula_correct.
  setoid_rewrite substitution_lookup_formula_correct. setoid_rewrite numerical_substitution_formula_correct.
  repeat setoid_rewrite code_eval_num. setoid_rewrite pc_eval_lift4. reflexivity.
Qed.

Theorem source_pc_instance_total M domain level count phi d X:
  exists out,source_pc_instance M domain level count phi d X out.
Proof.
  destruct(source_d0_recipe_total M domain level phi) as(d0&H0).
  destruct(source_dn_total M count d0) as(dn&HDN).
  destruct(source_role_reopening_total M X d) as(b&c&HR).
  destruct(numerical_substitution_total M dn b c(code_numeral M 2)(code_numeral M 2)) as(out&HS).
  exists out,d0,dn,b,c. auto.
Qed.

Theorem source_pc_dn_bounded M domain level count phi d0 dn:
  source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->
  source_bounded M phi(succM M count) ->source_d0_recipe M domain level phi d0 ->
  source_dn M count d0 dn ->source_bounded M dn(code_numeral M 2).
Proof.
  intros HD HL HB H0 HDN.
  apply(source_dn_bounded M count d0 dn(zeroM M)HDN).
  rewrite Arithmetic.add_comm,!Arithmetic.add_succ,Arithmetic.add_zero.
  exact(source_d0_recipe_bounded M domain level phi d0 count HD HL HB H0).
Qed.

Lemma source_pc_reopening_lookup M X d b c base i:
  source_role_reopening M X d b c ->(i<2)%nat ->
  substitution_lookup M b c(code_numeral M 2)base(code_numeral M i)
    (if Nat.eqb i 0 then d else X).
Proof.
  intros[H0 H1]HI. destruct i as[|[|i]];try lia.
  - apply(proj2(substitution_lookup_inside M b c(code_numeral M 2)base _ _
      (coding_zero_lt_succ M(code_numeral M 1)))).
    exact(proj1(substitution_lookup_inside M b c(code_numeral M 2)(zeroM M)_ _
      (coding_zero_lt_succ M(code_numeral M 1)))H0).
  - apply(proj2(substitution_lookup_inside M b c(code_numeral M 2)base _ _
      (coding_lt_succ M(code_numeral M 1)))).
    exact(proj1(substitution_lookup_inside M b c(code_numeral M 2)(zeroM M)_ _
      (coding_lt_succ M(code_numeral M 1)))H1).
Qed.

Theorem source_pc_instance_bounded M domain level count phi d X out k:
  source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->
  source_bounded M phi(succM M count) ->coding_lt M d k ->coding_lt M X k ->
  source_pc_instance M domain level count phi d X out ->source_bounded M out k.
Proof.
  intros HD HL HB HDk HXk(d0&dn&b&c&H0&HDN&HR&HS).
  apply(numerical_substitution_preserves_bound M dn b c(code_numeral M 2)(code_numeral M 2)out
    (code_numeral M 2)k(source_pc_dn_bounded M domain level count phi d0 dn HD HL HB H0 HDN)HS).
  intros i j HI HJ. destruct(source_numeral_initial_segment M 2 i HI) as(n&HN&->).
  pose proof(substitution_lookup_functional M _ _ _ _ _ j _ HJ
    (source_pc_reopening_lookup M X d b c(code_numeral M 2)n HR HN)) as E. subst j.
  destruct n as[|[|n]];try lia;assumption.
Qed.

Print Assumptions source_pc_instance_formula_correct.
Print Assumptions source_pc_instance_total.
Print Assumptions source_pc_dn_bounded.
Print Assumptions source_pc_instance_bounded.
