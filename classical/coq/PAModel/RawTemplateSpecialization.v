(** Specialization of a finite formula template at arbitrary model-valued
    names. The internally coded formula may still be nonstandard in size. *)
From PAModel Require Import Model FiniteCoding CodeExpressions CodeDescent NumericalProofs
  ProofTemplates NamedLeibnizSteps TemplateNamedSubstitution TemplateNamedExclusions
  TemplateBinderFresh StoppingInstantiation QuotientAtomTemplates.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Theorem finite_template_specialization M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff)
  rho X Y env fresh x y k :
  code_relation M rho X x -> code_relation M rho Y y ->
  code_relation M rho fresh k -> x<>zeroM M -> x<>y ->
  coding_lt M x k -> coding_lt M y k ->
  (forall idx v,code_relation M rho (env idx) v -> v<>x) ->
  ns_proof M rho (E_wim
    (E_wal X (template_set_formula (X .: env) fresh phi))
    (template_set_formula (Y .: env) fresh phi)).
Proof.
  intros HX HY HK H0 HXY HXK HYK Henv.
  set (A:=template_set_formula (X .: env) fresh phi).
  set (B:=template_set_formula (Y .: env) fresh phi).
  destruct (code_relation_total M A rho) as [a HA].
  destruct (code_relation_total M B rho) as [b HB].
  assert (Habs:NamedBinderFresh.named_binder_absent M a y).
  { exact (template_set_formula_binder_absent M phi (X .: env) fresh rho k y HK HYK a HA). }
  assert (Hsub:NamedSubstitution.named_substitution M a x y b).
  { apply (template_set_formula_named_substitution M phi (X .: env) (Y .: env)
      fresh fresh rho rho k x y H0 HK HK HXK HYK);[|exact HA|exact HB].
    intros [|idx] u v HU HV;cbn in HU,HV.
    + rewrite (code_relation_functional M X rho u x HU HX),
        (code_relation_functional M Y rho v y HV HY). now left.
    + right. split;[exact (Henv idx u HU)|].
      symmetry. exact (code_relation_functional M (env idx) rho u v HU HV). }
  exact (proj1 (ns_stopping_instantiation M rho X Y A B x y a b HX HY HA HB HXY Habs Hsub)).
Qed.

Print Assumptions finite_template_specialization.
