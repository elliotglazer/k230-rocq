(** Fixed names for consuming the numerical bootstrap: marker 1, witness 3,
    and internal marker-matrix binder 2. *)
From PAModel Require Import Model Arithmetic FiniteCoding Pairing CodeExpressions CodeDescent
  NumericalProofs ProofClosure ProofTemplates TemplateCD TemplatePropositional
  ProofMacros QuantifierMacros NumericalEquality NumericalBootstrap TargetNumeralLift
  FreshNames TemplateBinderFresh TemplateFormulaFresh NamedExistential.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
Unset Implicit Arguments.

Definition specialized_member_expression := E_wex (CEconst 3) (E_wel (CEconst 1) (CEconst 3)).
Definition specialized_marker_expression :=
  E_wal (CEconst 2) (E_wim (E_wel (CEconst 2) (CEconst 1)) (CEconst 1)).

Lemma generalized_member_program input domain witness :
  proof_macro [] [E_k230 input domain witness; witness]
    (E_wex witness (E_wel domain witness)).
Proof.
  set (N := E_wel domain witness).
  set (R := E_wal domain (E_wim N
    (E_wex input (E_wa witness (E_wal input
      (E_wim (E_ksubset input domain witness) (E_krequest domain witness witness))))))).
  assert (HBody : proof_macro [] [E_k230 input domain witness;witness]
    (E_wim (E_wa (E_wim witness N) R) N)).
  { apply macro_discharge,macro_deduction. eapply md_mp.
    - apply md_global,PM_input. now right;left.
    - eapply md_mp;[apply md_hyp;now left|].
      apply md_global,PM_template,bootstrap_projection_left. }
  apply (PM_mp (E_k230 input domain witness)).
  - apply PM_input. now left.
  - change (proof_macro [] [E_k230 input domain witness;witness]
      (E_wim (E_wex witness (E_wa (E_wim witness N) R)) (E_wex witness N))).
    apply macro_exists_monotone. exact HBody.
Qed.

Lemma numerical_three M : numerically_provable M (code_numeral M 3).
Proof.
  apply (numerical_equality_reflexivity M (zeroM M)).
  exists (zeroM M). split;[apply pair_zero|].
  rewrite (Arithmetic.mul_comm M),Arithmetic.mul_zero,Arithmetic.add_zero. reflexivity.
Qed.

Theorem numerical_marker_one_has_domain_member M env f :
  code_relation M env specialized_member_expression f -> numerically_provable M f.
Proof.
  intro HF. apply (unguarded_macro_sound M env
    [E_k230 (CEconst 4) (CEconst 1) (CEconst 3);CEconst 3] specialized_member_expression).
  - intros e [<-|[<-|[]]] q HQ.
    + exact (bootstrap_fixed_core M env 4 1 3 q ltac:(lia) ltac:(lia) HQ).
    + change (q=code_numeral M 3) in HQ. subst q. apply numerical_three.
  - apply generalized_member_program.
  - exact HF.
Qed.

Lemma fixed_name_avoids M env i j : i<>j ->
  expression_name_avoids M env (code_numeral M j) (CEconst i).
Proof.
  intros Hij f HF. change (f=code_numeral M i) in HF. subst f.
  exact (target_numerals_distinct M i j Hij).
Qed.

Theorem specialized_marker_fresh_three M env f :
  code_relation M env specialized_marker_expression f ->
  formula_fresh M f (code_numeral M 3).
Proof.
  apply (expression_fresh_universal M env (code_numeral M 3) (CEconst 2)
    (E_wim (E_wel (CEconst 2) (CEconst 1)) (CEconst 1))).
  - apply fixed_name_avoids. lia.
  - apply expression_fresh_implication.
    + apply (expression_fresh_atom M env 1 (CEconst 2) (CEconst 1) (code_numeral M 3)).
      * now left.
      * apply fixed_name_avoids. lia.
      * apply fixed_name_avoids. lia.
    + apply expression_fresh_one. exact (target_numerals_distinct M 3 0 ltac:(lia)).
Qed.

Theorem bootstrap_false_fresh_one M :
  formula_fresh M (code_numeral M 1) (code_numeral M 1).
Proof. apply formula_fresh_one. exact (target_numerals_distinct M 1 0 ltac:(lia)). Qed.

Theorem bootstrap_false_fresh_three M :
  formula_fresh M (code_numeral M 1) (code_numeral M 3).
Proof. apply formula_fresh_one. exact (target_numerals_distinct M 3 0 ltac:(lia)). Qed.

Theorem specialized_member_exists M : exists member exmember,
  membership_graph M (code_numeral M 1) (code_numeral M 3) member /\
  named_exists_graph M (code_numeral M 3) member exmember /\
  numerically_provable M exmember.
Proof.
  set (env := fun _ : nat => zeroM M).
  destruct (code_relation_total M (E_wel (CEconst 1) (CEconst 3)) env) as [member HM].
  destruct (code_relation_total M specialized_member_expression env) as [exmember HE].
  exists member,exmember. split.
  - exact (expression_tagged_graph M env 1 (CEconst 1) (CEconst 3)
      (code_numeral M 1) (code_numeral M 3) member eq_refl eq_refl HM).
  - split.
    + exact (proj1 (named_exists_expression M env (CEconst 3)
        (E_wel (CEconst 1) (CEconst 3)) (code_numeral M 3) member exmember eq_refl HM) HE).
    + exact (numerical_marker_one_has_domain_member M env exmember HE).
Qed.

Theorem bootstrap_marker_domain_package M : exists marker empty dom host,
  named_exists_graph M (code_numeral M 1) marker empty /\
  numerically_provable M empty /\
  membership_graph M (code_numeral M 1) (code_numeral M 3) dom /\
  named_exists_graph M (code_numeral M 3) dom host /\
  numerically_provable M host /\ formula_fresh M marker (code_numeral M 3).
Proof.
  set (env := fun _ : nat => zeroM M).
  destruct (code_relation_total M specialized_marker_expression env) as [marker HM].
  destruct (code_relation_total M bootstrap_empty_expression env) as [empty HE].
  destruct (specialized_member_exists M) as [dom [host [HD [HH PH]]]].
  exists marker,empty,dom,host. split.
  - exact (proj1 (named_exists_expression M env (CEconst 1) specialized_marker_expression
      (code_numeral M 1) marker empty eq_refl HM) HE).
  - split;[exact (numerical_empty_marker_exists M env empty HE)|].
    split;[exact HD|]. split;[exact HH|]. split;[exact PH|].
    exact (specialized_marker_fresh_three M env marker HM).
Qed.

Print Assumptions numerical_marker_one_has_domain_member.
Print Assumptions specialized_marker_fresh_three.
Print Assumptions bootstrap_false_fresh_one.
Print Assumptions bootstrap_false_fresh_three.
Print Assumptions specialized_member_exists.
Print Assumptions bootstrap_marker_domain_package.
