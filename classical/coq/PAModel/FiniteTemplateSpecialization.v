(** Specialization of one finite source binder to an arbitrary model name.
    The allocation base is above all free names and the replacement name. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions NumericalProofs
  ProofTemplates ProofClosure NumericalVacuitySteps NamedLeibnizSteps NamedSpecialization
  NamedSubstitution NamedSubstitutionRules TemplateNamedSubstitution TemplateNamedExclusions
  TemplateBinderFresh NamedBinderFresh QuotientAtomTemplates.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
From FOL Require Import FullSyntax Arithmetics.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Theorem finite_template_specialize M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff)
  rho env eta fresh k term y :
  (forall i,code_relation M rho (env i) (eta i)) ->
  (forall i,coding_lt M (eta i) k) ->
  code_relation M rho fresh k -> code_relation M rho term y ->
  coding_lt M (zeroM M) k -> coding_lt M y k ->
  ns_proof M rho (template_set_formula env fresh (quant All phi)) ->
  ns_proof M rho (template_set_formula (term .: env) (CEadd fresh (CEconst 1)) phi).
Proof.
  intros HE HElt HK HY Hpos Hylt HP out Hout.
  set (body := template_set_formula (fresh .: env) (CEadd fresh (CEconst 1)) phi).
  destruct (code_relation_total M body rho) as [a Ha].
  destruct (code_relation_total M (E_wal fresh body) rho) as [allf Hall].
  assert (Hallg : universal_graph M k a allf).
  { exact (expression_universal_graph M rho fresh body k a allf HK Ha Hall). }
  assert (Hsub : named_substitution M a k y out).
  { apply (template_set_formula_named_substitution M phi
      (fresh .: env) (term .: env) (CEadd fresh (CEconst 1))
      (CEadd fresh (CEconst 1)) rho rho (succM M k) k y).
    - exact (template_lt_different M (zeroM M) k Hpos).
    - now apply template_fresh_increment_graph.
    - now apply template_fresh_increment_graph.
    - apply coding_lt_succ.
    - exact (coding_lt_trans M y k (succM M k) Hylt (coding_lt_succ M k)).
    - intros [|i] u u' Hu Hu';cbn in Hu,Hu'.
      + rewrite (code_relation_functional M fresh rho u k Hu HK),
          (code_relation_functional M term rho u' y Hu' HY).
        left;auto.
      + rewrite (code_relation_functional M (env i) rho u (eta i) Hu (HE i)),
          (code_relation_functional M (env i) rho u' (eta i) Hu' (HE i)).
        right;split;[|reflexivity].
        pose proof (template_lt_different M (eta i) k (HElt i));congruence.
    - exact Ha.
    - exact Hout. }
  assert (Hax : named_binder_absent M a k).
  { apply (template_set_formula_binder_exclusion M phi (fresh .: env)
      (CEadd fresh (CEconst 1)) rho (succM M k) k).
    - now apply template_fresh_increment_graph.
    - apply template_allocations_avoid_below,coding_lt_succ.
    - exact Ha. }
  assert (Hay : named_binder_absent M a y).
  { apply (template_set_formula_binder_exclusion M phi (fresh .: env)
      (CEadd fresh (CEconst 1)) rho (succM M k) y).
    - now apply template_fresh_increment_graph.
    - apply template_allocations_avoid_below.
      exact (coding_lt_trans M y k (succM M k) Hylt (coding_lt_succ M k)).
    - exact Ha. }
  destruct (code_relation_total M (E_wim (CEvar 0) (CEvar 1))
    (arguments2 allf out (zeroM M))) as [result Hresult].
  apply (numerical_mp M allf out result).
  - apply HP. exact Hall.
  - exact (numerical_named_specialization M a k y out allf result
      (template_lt_different M y k Hylt) Hax Hay Hsub Hallg Hresult).
  - exact Hresult.
Qed.

Print Assumptions finite_template_specialize.
