(** Identity parameter graphs calibrate finite literal source formulas
    without normalizing their potentially enormous arithmetic code numerals. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes
  SourceFiniteParameters SourceNumeralLift SetSchemaConstructors SchemaConstructorBounds SubstitutionSource.
From FOL Require Import FullSyntax.
From Undecidability.FOL Require Import Syntax.BinSig Sets.Signatures.
Unset Implicit Arguments.

Theorem source_parameter_identity_calibration {ff} M
    (phi:@Core.form sig_empty ZFSignature.ZF_pred_sig full_operators ff) :forall names rho,
  (forall i,code_relation M rho (names i)(code_numeral M i)) ->
  code_relation M rho (source_parameter_expression names phi)(code_numeral M(sf_encode phi)).
Proof.
  induction phi;intros names rho HNames.
  - reflexivity.
  - destruct P;cbn [source_parameter_expression sf_encode];
      apply (proj2 (schema_expression_graph M rho _ _ _ _ _ _ (HNames _)(HNames _)));apply sf_make_numeral.
  - cbn [source_parameter_expression sf_encode]. destruct b0.
    all: apply (proj2 (schema_expression_graph M rho _ _ _ _ _ _
      (IHphi1 names rho HNames)(IHphi2 names rho HNames)));apply sf_make_numeral.
  - assert (HUp:forall i,code_relation M rho (source_parameter_up names i)(code_numeral M i)).
    { intros [|i];[reflexivity|]. cbn [source_parameter_up].
      exists (code_numeral M i),(code_numeral M 1). split;[exact(HNames i)|]. split;[reflexivity|].
      exact (Arithmetic.succ_as_add M (code_numeral M i)). }
    cbn [source_parameter_expression sf_encode]. destruct q.
    + apply (proj2 (schema_expression_graph M rho SFAll _ (CEconst 0) _ (zeroM M) _
        (IHphi (source_parameter_up names) rho HUp) eq_refl)). exact (sf_make_numeral M SFAll (sf_encode phi) 0).
    + apply (proj2 (schema_expression_graph M rho SFEx _ (CEconst 0) _ (zeroM M) _
        (IHphi (source_parameter_up names) rho HUp) eq_refl)). exact (sf_make_numeral M SFEx (sf_encode phi) 0).
Qed.

Print Assumptions source_parameter_identity_calibration.
