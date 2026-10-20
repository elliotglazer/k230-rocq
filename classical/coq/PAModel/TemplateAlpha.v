(** Proof-producing alpha conversion of a binder over a finite source
    template. The body's internal allocation base stays fixed. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT
  CodeExpressions NumericalProofs CodeDescent CodeTags FreshNames
  NamedSubstitutionRules NamedSubstitution NamedBinderFresh NamedAlpha
  QuotientAtomTemplates TemplateNamedSubstitution TemplateNamedExclusions TemplateBinderRange.
From FOL Require Import FullSyntax Arithmetics.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Definition alpha_template_environment i : code_expr :=
  match i with 0 => CEvar 1 | S j => CEvar (2+j) end.
Definition alpha_template_values M k x (rho : nat -> carrier M) := k .: x .: rho.
Definition alpha_template_body M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) rho k x f :=
  code_relation M (alpha_template_values M k x rho)
    (template_set_formula alpha_template_environment (CEvar 0) phi) f.

Lemma alpha_template_environment_replace M rho k x y :
  (forall i, rho i<>x) ->
  forall i, expression_named_replace M (alpha_template_values M k x rho)
    (alpha_template_values M k y rho) x y
    (alpha_template_environment i) (alpha_template_environment i).
Proof.
  intros H [|i] u v Hu Hv; cbn [alpha_template_environment alpha_template_values code_relation] in Hu,Hv;
    subst u v.
  - now left.
  - right. split; [apply H|reflexivity].
Qed.

Theorem alpha_template_substitution M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) rho k x y f v :
  x<>zeroM M -> (forall i, rho i<>x) ->
  template_allocations_avoid M phi k x -> template_allocations_avoid M phi k y ->
  alpha_template_body M phi rho k x f -> alpha_template_body M phi rho k y v ->
  named_substitution M f x y v.
Proof.
  intros Hx Hr Hax Hay Hf Hv.
  exact (template_set_formula_named_substitution_exclusions M phi
    alpha_template_environment alpha_template_environment (CEvar 0) (CEvar 0)
    (alpha_template_values M k x rho) (alpha_template_values M k y rho) k x y
    Hx eq_refl eq_refl Hax Hay (alpha_template_environment_replace M rho k x y Hr) f v Hf Hv).
Qed.

Theorem alpha_template_universal M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff)
  rho k x y f v allf allv forward backward :
  x<>zeroM M -> x<>y -> (forall i, rho i<>x) ->
  template_allocations_avoid M phi k x -> template_allocations_avoid M phi k y ->
  alpha_template_body M phi rho k x f -> alpha_template_body M phi rho k y v ->
  formula_fresh M f y ->
  universal_graph M x f allf -> universal_graph M y v allv ->
  implication_graph M allf allv forward -> implication_graph M allv allf backward ->
  named_substitution M f x y v /\ numerically_provable M forward /\ numerically_provable M backward.
Proof.
  intros Hx Hxy Hr Hax Hay Hf Hv Hfresh Hallf Hallv HF HB.
  pose proof (alpha_template_substitution M phi rho k x y f v Hx Hr Hax Hay Hf Hv) as Hsub.
  split; [exact Hsub|]. apply (numerical_named_alpha M f x y v allf allv forward backward);
    try assumption.
  exact (template_set_formula_binder_exclusion M phi alpha_template_environment
    (CEvar 0) (alpha_template_values M k x rho) k x eq_refl Hax f Hf).
Qed.

(** This theorem constructs the new name, the substituted body, both
    quantified formulas, and actual numerical K proofs in both directions. *)
Theorem alpha_template_universal_total M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) rho k x f allf :
  x<>zeroM M -> coding_lt M x k -> (forall i, rho i<>x) ->
  alpha_template_body M phi rho k x f -> universal_graph M x f allf ->
  exists y v allv forward backward,
    y=template_new_name M phi k f x /\ coding_lt M f y /\ coding_lt M x y /\
    alpha_template_body M phi rho k y v /\ named_substitution M f x y v /\
    universal_graph M y v allv /\ implication_graph M allf allv forward /\
    implication_graph M allv allf backward /\
    numerically_provable M forward /\ numerically_provable M backward.
Proof.
  intros Hx Hxk Hr Hf Hallf. set (y:=template_new_name M phi k f x).
  destruct (template_new_name_above M phi k f x) as [Hfy Hxy].
  change (coding_lt M f y) in Hfy. change (coding_lt M x y) in Hxy.
  destruct (code_relation_total M
    (template_set_formula alpha_template_environment (CEvar 0) phi)
    (alpha_template_values M k y rho)) as [v Hv].
  destruct (tagged_pair_total M 2 y v) as [allv Hallv].
  apply universal_graph_tagged in Hallv.
  destruct (code_relation_total M (E_wim (CEvar 0) (CEvar 1))
    (arguments2 allf allv (zeroM M))) as [forward HF].
  destruct (code_relation_total M (E_wim (CEvar 0) (CEvar 1))
    (arguments2 allv allf (zeroM M))) as [backward HB].
  destruct (alpha_template_universal M phi rho k x y f v allf allv forward backward
    Hx (@Peano.lt_neq (carrier M) (raw_interpretation M)
      (fun ax H rho => axioms M ax rho H) x y Hxy) Hr
    (template_allocations_avoid_below M phi k x Hxk)
    (template_new_name_avoids M phi k f x) Hf Hv
    (formula_above_is_fresh M f y Hfy) Hallf Hallv HF HB) as [Hsub [PF PB]].
  exists y,v,allv,forward,backward. repeat split; assumption || reflexivity.
Qed.

Print Assumptions alpha_template_substitution.
Print Assumptions alpha_template_universal.
Print Assumptions alpha_template_universal_total.
