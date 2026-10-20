(** Reusable specialization of a fixed old finite certificate. The actual
    old thm230 proof is an explicit input, not an axiom-image promise. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NamedLeibnizSteps NumericalEquivalence
  OldNamedSyntaxBridge ThmConstructorBridge ExtensionalityImage ProofTemplates QuotientAtomTemplates
  FiniteNamedPolicies FinitePolicyBounded FiniteTemplateRebase FiniteTemplateInstantiation
  FiniteTemplateEvaluation ZFCFiniteAxiomTemplates TargetNumeralLift.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
From Stdlib Require Import Lia Lists.List.
Unset Implicit Arguments.

Definition original_named_expression {ff} (oldphi:isolated_old_form ff) :=
  named_policy_formula true (named_bottom_expression (CEconst 0)) depth_binder_policy
    (fun index=>CEconst (2*index+1)) (CEconst 0) (isolated_formula oldphi).

Lemma original_named_value {ff} (oldphi:isolated_old_form ff) : code_value (fun _=>0) (original_named_expression oldphi) =
  OldK230L.Comp_Prop230.tau (OldZF.Std_tr.tr OldZF.Std_glue.eta0 oldphi).
Proof. symmetry;exact (isolated_tr_code_value oldphi OldZF.Std_glue.eta0 (CEconst 0) (fun _=>0)). Qed.

Theorem finite_original_closed_template {ff} M (oldphi:isolated_old_form ff) rho fresh k :
  bounded 0 (isolated_formula oldphi) ->
  OldK230L.Thm230.thm230 (OldK230L.Comp_Prop230.tau (OldZF.Std_tr.tr OldZF.Std_glue.eta0 oldphi)) ->
  code_relation M rho fresh k -> coding_lt M (zeroM M) k ->
  ns_proof M rho (template_set_formula (fun _=>CEconst 0) fresh (isolated_formula oldphi)).
Proof.
  intros HB HCertificate HK H0 g HG.
  assert (HP : ns_proof M (fun _=>zeroM M) (original_named_expression oldphi)).
  { apply current_certificate_expression;rewrite original_named_value.
    exact (original_thm230_to_current _ HCertificate). }
  destruct (code_relation_total M (original_named_expression oldphi) (fun _=>zeroM M)) as [f HF].
  apply (numerical_implies_apply M f g).
  - apply (proj1 (finite_bounded_depth_to_sequential_codes M (isolated_formula oldphi) 0
      (fun _=>zeroM M) rho true (fun index=>CEconst (2*index+1)) (fun _=>CEconst 0)
      (CEconst 0) fresh (CEconst 0)
      (fun index=>code_numeral M (2*index+1)) (fun _=>zeroM M) k f g
      HB ltac:(intros;lia) ltac:(intro;reflexivity) ltac:(intro;reflexivity)
      ltac:(intros i n Hn;change (code_numeral M (2*n)<>code_numeral M 0);
        apply target_numerals_distinct;lia)
      HK (template_hygienic_below M (isolated_formula oldphi) (fun _=>zeroM M) k H0 (fun _=>H0)) HF HG)).
  - exact (HP f HF).
Qed.

Lemma isolated_forall_prefix {ff} n (oldbody:isolated_old_form ff) :
  isolated_formula (OldUndecidability.FOL.Syntax.Core.FullSyntax.forall_times n oldbody) =
  template_all_prefix n (isolated_formula oldbody).
Proof.
  induction n;[reflexivity|].
  change (@C.quant Undecidability.FOL.Syntax.BinSig.sig_empty Undecidability.FOL.Sets.Signatures.ZFSignature.ZF_pred_sig C.FullSyntax.full_operators (isolated_flag ff) C.FullSyntax.All (isolated_formula (OldUndecidability.FOL.Syntax.Core.FullSyntax.forall_times n oldbody)) =
    @C.quant Undecidability.FOL.Syntax.BinSig.sig_empty Undecidability.FOL.Sets.Signatures.ZFSignature.ZF_pred_sig C.FullSyntax.full_operators (isolated_flag ff) C.FullSyntax.All (template_all_prefix n (isolated_formula oldbody))).
  now rewrite IHn.
Qed.

Theorem finite_original_prefix_instance {ff} M (oldbody:isolated_old_form ff) n args rho fresh k eta :
  bounded 0 (isolated_formula (OldUndecidability.FOL.Syntax.Core.FullSyntax.forall_times n oldbody)) ->
  OldK230L.Thm230.thm230 (OldK230L.Comp_Prop230.tau (OldZF.Std_tr.tr OldZF.Std_glue.eta0
    (OldUndecidability.FOL.Syntax.Core.FullSyntax.forall_times n oldbody))) ->
  length args=n -> code_relation M rho fresh k -> coding_lt M (zeroM M) k ->
  (forall index,code_relation M rho (template_bind_arguments args (fun _=>CEconst 0) index) (eta index)) ->
  (forall index,coding_lt M (eta index) k) ->
  (forall arg,In arg args -> exists v,code_relation M rho arg v /\ coding_lt M v k) ->
  ns_proof M rho (template_set_formula (template_bind_arguments args (fun _=>CEconst 0)) fresh
    (isolated_formula oldbody)).
Proof.
  intros HB HCert HLen HK H0 HEnv HValues HArgs f HF.
  set (high:=template_advance_name M k (length args)).
  assert (HHigh : ns_proof M rho (template_set_formula
    (template_bind_arguments args (fun _=>CEconst 0))
    (template_advance_fresh fresh (length args)) (isolated_formula oldbody))).
  { apply (finite_template_specialize_list M (isolated_formula oldbody) args rho
      (fun _=>CEconst 0) (fun _=>zeroM M) fresh k).
    - intro index;reflexivity.
    - intro index;exact H0.
    - exact HK.
    - exact H0.
    - exact HArgs.
    - rewrite HLen,<-isolated_forall_prefix.
      exact (finite_original_closed_template M _ rho fresh k HB HCert HK H0). }
  destruct (code_relation_total M (template_set_formula
    (template_bind_arguments args (fun _=>CEconst 0))
    (template_advance_fresh fresh (length args)) (isolated_formula oldbody)) rho) as [g HG].
  assert (HH : template_hygienic M (isolated_formula oldbody) eta high).
  { apply template_hygienic_below.
    - exact (template_advance_name_above M _ (zeroM M) k H0).
    - intro index;apply template_advance_name_above,HValues. }
  assert (HL : template_hygienic M (isolated_formula oldbody) eta k) by (apply template_hygienic_below;assumption).
  assert (EG : template_evaluation M (isolated_formula oldbody) eta high g).
  { apply (proj1 (template_evaluation_graph M (isolated_formula oldbody)
      (template_bind_arguments args (fun _=>CEconst 0)) (template_advance_fresh fresh (length args))
      rho eta high g HEnv (template_advance_fresh_graph M _ rho fresh k HK)));exact HG. }
  assert (EF : template_evaluation M (isolated_formula oldbody) eta k f).
  { apply (proj1 (template_evaluation_graph M (isolated_formula oldbody)
      (template_bind_arguments args (fun _=>CEconst 0)) fresh rho eta k f HEnv HK));exact HF. }
  apply (numerical_implies_apply M g f).
  - exact (proj1 (finite_template_rebase M (isolated_formula oldbody) eta high k g f HH HL EG EF)).
  - exact (HHigh g HG).
Qed.

Print Assumptions finite_original_closed_template.
Print Assumptions finite_original_prefix_instance.
