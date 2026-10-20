(** An actual fixed K230 certificate, transported into every PA model and
    normalized to the precise marker-1, quotation-base-4 source axiom image. *)
From PAModel Require Import ExtensionalityCertificateBridge OldNamedSyntaxBridge
  ExtensionalityNormalization Model CodeExpressions SourceNumeralLift TargetNumeralLift
  NumericalProofs NumericalEquivalence ProofMacros NamedLeibnizSteps BootstrapSpecializations
  FixedAxiomCertificates ZFCFiniteAxiomTemplates ZFCFiniteSourceCodes
  NumericalQuotation QuotationQTrans QuotientAtomTemplates.
From OldFixedTarget Require Extensionality230.
From OldK230S Require KQuotFormula.
From OldZF Require Std_glue.
From K230S Require KCode230.
From K230L Require Import Thm230.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
Unset Implicit Arguments.

Lemma old_extensionality_expression_value :
  code_value (fun _=>0) old_extensionality_expression =
  OldFixedTarget.Extensionality230.old_quotient_extensionality_code.
Proof.
  symmetry.
  pose proof (isolated_tr_code_value
    (OldK230S.KQuotFormula.qtrans
      (@OldUndecidability.FOL.Syntax.Core.var
        OldUndecidability.FOL.Syntax.BinSig.sig_empty 0)
      OldUndecidability.FOL.Sets.minZF.ax_ext')
    OldZF.Std_glue.eta0 (CEconst 0) (fun _=>0)) as H.
  rewrite isolated_quoted_extensionality_exact in H.
  exact H.
Qed.

Lemma old_marker_expression_value :
  code_value (fun _=>0)
    (E_wim specialized_marker_expression old_extensionality_expression) =
  OldFixedTarget.Extensionality230.marker_extensionality_code.
Proof.
  rewrite current_marker_extensionality_code_exact,code_value_wim,
    old_extensionality_expression_value.
  reflexivity.
Qed.

Theorem current_certificate_expression M expression :
  thm230 (code_value (fun _=>0) expression) ->
  ns_proof M (fun _=>zeroM M) expression.
Proof.
  intros HP result HR.
  pose proof (code_relation_numeral M (fun _=>0) expression) as HC.
  assert (E : result=code_numeral M (code_value (fun _=>0) expression)).
  { exact (code_relation_functional M expression (fun _=>zeroM M) _ _ HR HC). }
  subst result. apply thm230_numeral_lift. exact HP.
Qed.

Theorem actual_extensionality_marker_expression M :
  ns_proof M (fun _=>zeroM M)
    (E_wim specialized_marker_expression old_extensionality_expression).
Proof.
  apply current_certificate_expression.
  rewrite old_marker_expression_value.
  exact current_marker_extensionality_certificate.
Qed.

Theorem actual_extensionality_marker_image M marker f q :
  code_relation M (fun _=>zeroM M) specialized_marker_expression marker ->
  zfc_source_graph M ZFCExt f ->
  numerical_quotation M f (zeroM M) (zeroM M) (zeroM M)
    (code_numeral M 4) (code_numeral M 1) q ->
  numerical_implies M marker q.
Proof.
  intros HM HF HQ.
  destruct (code_relation_total M old_extensionality_expression
    (fun _=>zeroM M)) as [old HO].
  apply (numerical_implies_trans M marker old q).
  - apply (proj1 (numerical_implies_expression M (fun _=>zeroM M)
      specialized_marker_expression old_extensionality_expression marker old HM HO)).
    apply actual_extensionality_marker_expression.
  - exact (proj1 (extensionality_old_code_normalization M old q HO
      (finite_source_quotation_graph M ax_ext' f q HF HQ))).
Qed.

Print Assumptions old_extensionality_expression_value.
Print Assumptions old_marker_expression_value.
Print Assumptions current_certificate_expression.
Print Assumptions actual_extensionality_marker_expression.
Print Assumptions actual_extensionality_marker_image.
