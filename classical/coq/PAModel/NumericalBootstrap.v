(** Direct fixed K certificates for an empty marker and domain members.
    The proof programs use only the actual numerical K core and logical
    rows. They do not import the original set-theory library. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  ProofClosure ProofTemplates TemplateCD TemplatePropositional ProofMacros QuantifierMacros
  NumericalVacuitySteps NumericalVacuity FreshNames KInternalLogic
  TargetNumeralLift FixedSourceBounds.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
Unset Implicit Arguments.

Lemma bootstrap_projection_left G p q :
  template_proof G (E_wim (E_wa p q) p).
Proof.
  apply template_discharge,template_deduction.
  apply (template_der_andl G [E_wa p q] p q),dhyp. now left.
Qed.
Lemma bootstrap_projection_right G p q :
  template_proof G (E_wim (E_wa p q) q).
Proof.
  apply template_discharge,template_deduction.
  apply (template_der_andr G [E_wa p q] p q),dhyp. now left.
Qed.

Lemma bootstrap_exists_projection G inputs x p q :
  proof_macro G inputs (E_vac x p) ->
  proof_macro G inputs (E_wim (E_wex x (E_wa p q)) p).
Proof.
  intro HV. eapply macro_syl.
  - apply macro_exists_monotone,PM_template,bootstrap_projection_left.
  - eapply macro_syl.
    + apply macro_exists_monotone. exact HV.
    + apply PM_template,template_r6.
Qed.

Definition bootstrap_empty_expression :=
  E_wex (CEconst 1) (E_wal (CEconst 2)
    (E_wim (E_wel (CEconst 2) (CEconst 1)) (CEconst 1))).
Definition bootstrap_member_expression domain := E_wex (CEconst 2) (E_wel domain (CEconst 2)).
Definition bootstrap_domain_expression := E_wal (CEconst 4) (bootstrap_member_expression (CEconst 4)).
Definition bootstrap_empty_inputs :=
  [E_k230 (CEconst 3) (CEconst 2) (CEconst 1); E_vac (CEconst 3) (CEconst 1)].
Definition bootstrap_member_inputs domain := [E_k230 (CEconst 3) domain (CEconst 2); CEconst 2].
Definition bootstrap_domain_inputs := bootstrap_member_inputs (CEconst 4).

Lemma bootstrap_empty_program :
  proof_macro [] bootstrap_empty_inputs bootstrap_empty_expression.
Proof.
  set (N := E_wel (CEconst 2) (CEconst 1)).
  set (R := E_wal (CEconst 3)
    (E_wim (E_ksubset (CEconst 3) (CEconst 2) (CEconst 1))
      (E_krequest (CEconst 2) (CEconst 1) (CEconst 1)))).
  set (P := E_wex (CEconst 3) (E_wa (CEconst 1) R)).
  assert (HP : proof_macro [] bootstrap_empty_inputs (E_wim P (CEconst 1))).
  { apply bootstrap_exists_projection,PM_input. unfold bootstrap_empty_inputs. now right;left. }
  assert (HStep : proof_macro [] bootstrap_empty_inputs
    (E_wim (E_wim N P) (E_wim N (CEconst 1)))).
  { eapply PM_mp;[|apply PM_template,template_S].
    eapply PM_mp;[exact HP|apply PM_template,template_K]. }
  assert (HAll : proof_macro [] bootstrap_empty_inputs
    (E_wim (E_wal (CEconst 2) (E_wim N P))
      (E_wal (CEconst 2) (E_wim N (CEconst 1))))).
  { apply macro_all_monotone. exact HStep. }
  assert (HBody : proof_macro [] bootstrap_empty_inputs
    (E_wim (E_wa (E_wim (CEconst 1) N) (E_wal (CEconst 2) (E_wim N P)))
      (E_wal (CEconst 2) (E_wim N (CEconst 1))))).
  { eapply macro_syl;[apply PM_template,bootstrap_projection_right|exact HAll]. }
  apply (PM_mp (E_k230 (CEconst 3) (CEconst 2) (CEconst 1))).
  - apply PM_input. now left.
  - change (proof_macro [] bootstrap_empty_inputs
      (E_wim (E_wex (CEconst 1)
        (E_wa (E_wim (CEconst 1) N) (E_wal (CEconst 2) (E_wim N P))))
        (E_wex (CEconst 1) (E_wal (CEconst 2) (E_wim N (CEconst 1)))))).
    apply macro_exists_monotone. exact HBody.
Qed.

Lemma bootstrap_member_program domain :
  proof_macro [] (bootstrap_member_inputs domain) (bootstrap_member_expression domain).
Proof.
  set (N := E_wel domain (CEconst 2)).
  set (R := E_wal domain (E_wim N
    (E_wex (CEconst 3) (E_wa (CEconst 2) (E_wal (CEconst 3)
      (E_wim (E_ksubset (CEconst 3) domain (CEconst 2))
        (E_krequest domain (CEconst 2) (CEconst 2)))))))).
  assert (HBody : proof_macro [] (bootstrap_member_inputs domain)
    (E_wim (E_wa (E_wim (CEconst 2) N) R) N)).
  { apply macro_discharge,macro_deduction.
    eapply md_mp.
    - apply md_global,PM_input. unfold bootstrap_member_inputs. now right;left.
    - eapply md_mp;[apply md_hyp;now left|].
      apply md_global,PM_template,bootstrap_projection_left. }
  apply (PM_mp (E_k230 (CEconst 3) domain (CEconst 2))).
  - apply PM_input. now left.
  - change (proof_macro [] (bootstrap_member_inputs domain)
      (E_wim (E_wex (CEconst 2) (E_wa (E_wim (CEconst 2) N) R))
        (E_wex (CEconst 2) N))).
    apply macro_exists_monotone. exact HBody.
Qed.

Lemma bootstrap_domain_program :
  proof_macro [] bootstrap_domain_inputs bootstrap_domain_expression.
Proof. apply PM_gen,bootstrap_member_program. Qed.

Lemma bootstrap_fixed_core M env a b c f : c<>a -> c<>b ->
  code_relation M env (E_k230 (CEconst a) (CEconst b) (CEconst c)) f ->
  numerically_provable M f.
Proof.
  intros Hca Hcb HF.
  apply (numerical_K_core M (code_numeral M a) (code_numeral M b) (code_numeral M c) f).
  - exact (target_numerals_distinct M c a Hca).
  - exact (target_numerals_distinct M c b Hcb).
  - exact (proj1 (code_subst_graph M env
      (code_parameters (CEconst a) (CEconst b) (CEconst c) (CEconst 0))
      (code_parameters (code_numeral M a) (code_numeral M b) (code_numeral M c) (zeroM M))
      ltac:(intros [|[|[|i]]];reflexivity)
      (E_k230 (CEvar 0) (CEvar 1) (CEvar 2)) f) HF).
Qed.

Theorem numerical_empty_marker_exists M env f :
  code_relation M env bootstrap_empty_expression f -> numerically_provable M f.
Proof.
  intro HF. apply (unguarded_macro_sound M env bootstrap_empty_inputs bootstrap_empty_expression).
  - intros e [<-|[<-|[]]] q HQ.
    + exact (bootstrap_fixed_core M env 3 2 1 q ltac:(lia) ltac:(lia) HQ).
    + apply (numerical_vacuity M (code_numeral M 3) (code_numeral M 1) q).
      * apply formula_above_is_fresh. apply (proj2 (fixed_source_numeral_lt_iff M 1 3)). lia.
      * exact (proj1 (expression_vacuity_graph M env (CEconst 3) (CEconst 1)
          (code_numeral M 3) (code_numeral M 1) q eq_refl eq_refl) HQ).
  - exact bootstrap_empty_program.
  - exact HF.
Qed.

Theorem numerical_every_marker_has_domain_member M env f :
  code_relation M env bootstrap_domain_expression f -> numerically_provable M f.
Proof.
  intro HF. apply (unguarded_macro_sound M env bootstrap_domain_inputs bootstrap_domain_expression).
  - intros e [<-|[<-|[]]] q HQ.
    + exact (bootstrap_fixed_core M env 3 4 2 q ltac:(lia) ltac:(lia) HQ).
    + change (q=code_numeral M 2) in HQ. subst q.
      exact (numerical_gen M (zeroM M) (zeroM M) (code_numeral M 2)
        (numerical_truth M) (target_numeral_universal M 0 0)).
  - exact bootstrap_domain_program.
  - exact HF.
Qed.

Theorem numerical_fixed_marker_has_domain_member M env marker f : marker<>2 ->
  code_relation M env (bootstrap_member_expression (CEconst marker)) f ->
  numerically_provable M f.
Proof.
  intros Hmarker HF. apply (unguarded_macro_sound M env (bootstrap_member_inputs (CEconst marker))
    (bootstrap_member_expression (CEconst marker))).
  - intros e [<-|[<-|[]]] q HQ.
    + exact (bootstrap_fixed_core M env 3 marker 2 q ltac:(lia) ltac:(congruence) HQ).
    + change (q=code_numeral M 2) in HQ. subst q.
      exact (numerical_gen M (zeroM M) (zeroM M) (code_numeral M 2)
        (numerical_truth M) (target_numeral_universal M 0 0)).
  - apply bootstrap_member_program.
  - exact HF.
Qed.

Print Assumptions bootstrap_empty_program.
Print Assumptions bootstrap_domain_program.
Print Assumptions numerical_empty_marker_exists.
Print Assumptions numerical_every_marker_has_domain_member.
Print Assumptions numerical_fixed_marker_has_domain_member.
