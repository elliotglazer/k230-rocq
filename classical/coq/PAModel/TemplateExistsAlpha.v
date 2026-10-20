(** Proof-producing existential alpha conversion, followed by its finite
    template specialization. Encoded negation requires both names nonzero. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT
  CodeExpressions NumericalProofs CodeDescent CodeTags FreshNames ProofTemplates ProofMacros QuantifierMacros
  NumericalVacuitySteps NamedSubstitutionRules NamedSubstitution NamedBinderFresh NamedAlpha
  NamedExistential NamedLeibnizSteps TemplateBinderFresh TemplateFormulaFresh
  QuotientAtomTemplates TemplateNamedSubstitution TemplateNamedExclusions TemplateBinderRange TemplateAlpha.
From FOL Require Import FullSyntax Arithmetics.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Theorem numerical_named_exists_alpha M f x y v exf exv forward backward :
  x<>zeroM M -> y<>zeroM M -> x<>y ->
  named_binder_absent M f x -> formula_fresh M f y -> named_substitution M f x y v ->
  named_exists_graph M x f exf -> named_exists_graph M y v exv ->
  implication_graph M exf exv forward -> implication_graph M exv exf backward ->
  numerically_provable M forward /\ numerically_provable M backward.
Proof.
  intros Hx Hy Hxy Habs Hfresh Hsub Hexf Hexv HF HB.
  set (env:=code_parameters x y f v).
  set (A:=E_wal (CEvar 0) (E_wn (CEvar 2))).
  set (B:=E_wal (CEvar 1) (E_wn (CEvar 3))).
  destruct (code_relation_total M (E_wn (CEvar 2)) env) as [nf Hnf].
  destruct (code_relation_total M (E_wn (CEvar 3)) env) as [nv Hnv].
  destruct (code_relation_total M A env) as [allf HAf].
  destruct (code_relation_total M B env) as [allv HBv].
  assert (Hnfsub : named_substitution M nf x y nv).
  { apply (expression_ns_negation M env env x y (CEvar 2) (CEvar 3) Hx); [|exact Hnf|exact Hnv].
    intros a b Ha Hb. change (a=f) in Ha. change (b=v) in Hb. now subst a b. }
  assert (Hnabs : named_binder_absent M nf x).
  { apply (expression_binder_absent_negation M env x (CEvar 2)); [|exact Hnf].
    intros z Hz. change (z=f) in Hz. now subst z. }
  assert (Hnfresh : formula_fresh M nf y).
  { apply (expression_fresh_negation M env y (CEvar 2) Hy); [|exact Hnf].
    intros z Hz. change (z=f) in Hz. now subst z. }
  assert (HUf : universal_graph M x nf allf).
  { exact (expression_universal_graph M env (CEvar 0) (E_wn (CEvar 2)) x nf allf eq_refl Hnf HAf). }
  assert (HUv : universal_graph M y nv allv).
  { exact (expression_universal_graph M env (CEvar 1) (E_wn (CEvar 3)) y nv allv eq_refl Hnv HBv). }
  destruct (code_relation_total M (E_wim A B) env) as [fab Hfab].
  destruct (code_relation_total M (E_wim B A) env) as [fba Hfba].
  destruct (numerical_named_alpha M nf x y nv allf allv fab fba Hxy Hnabs Hnfresh Hnfsub HUf HUv
    (expression_implication_graph M env A B allf allv fab HAf HBv Hfab)
    (expression_implication_graph M env B A allv allf fba HBv HAf Hfba)) as [Pab Pba].
  assert (EF : code_relation M env (E_wn A) exf).
  { exact (proj2 (named_exists_expression M env (CEvar 0) (CEvar 2) x f exf eq_refl eq_refl) Hexf). }
  assert (EV : code_relation M env (E_wn B) exv).
  { exact (proj2 (named_exists_expression M env (CEvar 1) (CEvar 3) y v exv eq_refl eq_refl) Hexv). }
  split.
  - apply (unguarded_macro_sound M env ((E_wim B A)::nil) (E_wim (E_wn A) (E_wn B))
      (ProofMacros.macro_one_input M env (E_wim B A) fba Hfba Pba)).
    + apply macro_contra,PM_input. now left.
    + exact (proj2 (expression_implication_iff M env (E_wn A) (E_wn B) exf exv forward EF EV) HF).
  - apply (unguarded_macro_sound M env ((E_wim A B)::nil) (E_wim (E_wn B) (E_wn A))
      (ProofMacros.macro_one_input M env (E_wim A B) fab Hfab Pab)).
    + apply macro_contra,PM_input. now left.
    + exact (proj2 (expression_implication_iff M env (E_wn B) (E_wn A) exv exf backward EV EF) HB).
Qed.

Theorem alpha_template_exists_total M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) rho k x f exf :
  x<>zeroM M -> coding_lt M x k -> (forall i, rho i<>x) ->
  alpha_template_body M phi rho k x f -> named_exists_graph M x f exf ->
  exists y v exv forward backward,
    y=template_new_name M phi k f x /\ coding_lt M f y /\ coding_lt M x y /\
    alpha_template_body M phi rho k y v /\ named_substitution M f x y v /\
    named_exists_graph M y v exv /\ implication_graph M exf exv forward /\
    implication_graph M exv exf backward /\
    numerically_provable M forward /\ numerically_provable M backward.
Proof.
  intros Hx Hxk Hr Hf Hexf.
  destruct (tagged_pair_total M 2 x f) as [allf Hallf]. apply universal_graph_tagged in Hallf.
  destruct (alpha_template_universal_total M phi rho k x f allf Hx Hxk Hr Hf Hallf)
    as [y [v [allv [p [q [Ey [Hfy [Hxy [Hv [Hsub [Hallv [Hp [Hq [Pp Pq]]]]]]]]]]]]]].
  destruct (named_exists_graph_total M y v) as [exv Hexv].
  destruct (code_relation_total M (E_wim (CEvar 0) (CEvar 1))
    (arguments2 exf exv (zeroM M))) as [forward HF].
  destruct (code_relation_total M (E_wim (CEvar 0) (CEvar 1))
    (arguments2 exv exf (zeroM M))) as [backward HB].
  assert (Hy : y<>zeroM M).
  { intro E. rewrite E in Hxy. exact (coding_not_lt_zero M x Hxy). }
  assert (Habs : named_binder_absent M f x).
  { exact (template_set_formula_binder_exclusion M phi alpha_template_environment
      (CEvar 0) (alpha_template_values M k x rho) k x eq_refl
      (template_allocations_avoid_below M phi k x Hxk) f Hf). }
  destruct (numerical_named_exists_alpha M f x y v exf exv forward backward Hx Hy
    (@Peano.lt_neq (carrier M) (raw_interpretation M)
      (fun ax H rho => axioms M ax rho H) x y Hxy)
    Habs (formula_above_is_fresh M f y Hfy) Hsub Hexf Hexv HF HB) as [PF PB].
  exists y,v,exv,forward,backward. repeat split; assumption.
Qed.

Print Assumptions numerical_named_exists_alpha.
Print Assumptions alpha_template_exists_total.
