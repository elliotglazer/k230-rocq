(** Exact internally finite assignment table [ordinal,carrier,parameters]. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions NumericalProofs
 NumericalEnvironments NumericalSubstitutionMaps SourceRoleReopening SourceDnEnvironmentTail.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature |0.
#[local] Existing Instance PA_preds_signature |0.
Definition source_dn_assignment M count pb pc d X b c :=exists u v,
 environment_cons M pb pc count X u v(succM M count) /\
 environment_cons M u v(succM M count)d b c(succM M(succM M count)).
Definition source_dn_assignment_formula(count pb pc d X b c:term):form:=
 ∃∃(environment_cons_formula pb`[↑]`[↑] pc`[↑]`[↑] count`[↑]`[↑] X`[↑]`[↑]
 $1 $0 (σ count)`[↑]`[↑] ∧environment_cons_formula $1 $0 (σ count)`[↑]`[↑]
 d`[↑]`[↑] b`[↑]`[↑] c`[↑]`[↑] (σ(σ count))`[↑]`[↑]).
Local Opaque holds environment_cons_formula.
Theorem source_dn_assignment_formula_correct M rho count pb pc d X b c:
 holds M rho(source_dn_assignment_formula count pb pc d X b c)<->
 source_dn_assignment M(evalM M rho count)(evalM M rho pb)(evalM M rho pc)
 (evalM M rho d)(evalM M rho X)(evalM M rho b)(evalM M rho c).
Proof.
 unfold source_dn_assignment_formula,source_dn_assignment.
 repeat setoid_rewrite holds_ex. setoid_rewrite holds_and.
 setoid_rewrite environment_cons_formula_correct.
 unfold evalM. repeat setoid_rewrite eval_up. reflexivity.
Qed.
Theorem source_dn_assignment_total M count pb pc d X:exists b c,
 source_dn_assignment M count pb pc d X b c.
Proof.
 destruct(environment_cons_total M pb pc count X)as(u&v&n&HU).
 pose proof(proj1 HU)as E;subst n.
 destruct(environment_cons_total M u v(succM M count)d)as(b&c&n&HD).
 pose proof(proj1 HD)as E;subst n. exists b,c,u,v;auto.
Qed.
Lemma source_dn_assignment_zero M count pb pc d X b c:
 source_dn_assignment M count pb pc d X b c ->
 substitution_lookup M b c(succM M(succM M count))(zeroM M)(zeroM M)d.
Proof.
 intros(u&v&HU&HD). apply substitution_lookup_inside;[apply coding_zero_lt_succ|].
 apply(proj1(environment_lookup_inside M b c(succM M(succM M count))(zeroM M)d (coding_zero_lt_succ M(succM M count)))).
 exact(proj2(environment_cons_head M _ _ _ _ _ _ _ _ HD)eq_refl).
Qed.
Lemma source_dn_assignment_one M count pb pc d X b c:
 source_dn_assignment M count pb pc d X b c ->
 substitution_lookup M b c(succM M(succM M count))(zeroM M)(code_numeral M 1)X.
Proof.
 intros(u&v&HU&HD). apply substitution_lookup_inside;[apply coding_lt_succ_cancel,coding_zero_lt_succ|].
 apply(proj1(environment_lookup_inside M b c(succM M(succM M count))(code_numeral M 1)X
  (proj2(coding_lt_succ_cancel M (zeroM M)(succM M count))(coding_zero_lt_succ M count)))).
 apply(proj2(environment_cons_tail M _ _ _ _ _ _ _ _ _ HD)).
 exact(proj2(environment_cons_head M _ _ _ _ _ _ _ _ HU)eq_refl).
Qed.
Lemma source_dn_assignment_parameter M count pb pc d X b c i value:
 source_dn_assignment M count pb pc d X b c ->coding_lt M i count ->
 (substitution_lookup M b c(succM M(succM M count))(zeroM M)(succM M(succM M i))value
 <->beta M pb pc i value).
Proof.
 intros(u&v&HU&HD)HI. rewrite substitution_lookup_inside by
 (apply coding_lt_succ_cancel,coding_lt_succ_cancel;exact HI).
 rewrite <-environment_lookup_inside by
 (apply coding_lt_succ_cancel,coding_lt_succ_cancel;exact HI).
 rewrite(environment_cons_tail M _ _ _ _ _ _ _ _ _ HD).
 rewrite(environment_cons_tail M _ _ _ _ _ _ _ _ _ HU).
 apply environment_lookup_inside;exact HI.
Qed.
Lemma source_dn_assignment_empty M pb pc d X b c:
 source_dn_assignment M(zeroM M)pb pc d X b c ->source_role_reopening M X d b c.
Proof.
 intro H. split;[exact(source_dn_assignment_zero M _ _ _ _ _ _ _ H)|
 exact(source_dn_assignment_one M _ _ _ _ _ _ _ H)].
Qed.
Print Assumptions source_dn_assignment_formula_correct.
Print Assumptions source_dn_assignment_total.
Print Assumptions source_dn_assignment_parameter.
