(** Literal calibration of the fixed finite parameter compiler at identity names. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  ZFCFiniteSourceCodes SourceNumeralLift SourceFiniteParameters.
From FOL Require Import FullSyntax.
From Undecidability.FOL Require Import Syntax.BinSig Sets.Signatures.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Lemma source_parameter_identity_value {ff}
    (phi:@Core.form sig_empty ZFSignature.ZF_pred_sig full_operators ff) :
  forall names env,
  (forall i,code_value env(names i)=i) ->
  code_value env(source_parameter_expression names phi)=sf_encode phi.
Proof.
  induction phi; intros names env HNames.
  - reflexivity.
  - destruct P; cbn [source_parameter_expression sf_encode]; rewrite sf_make_value;
      now rewrite !HNames.
  - destruct b0; cbn [source_parameter_expression sf_encode]; rewrite sf_make_value;
      rewrite (IHphi1 names env HNames),(IHphi2 names env HNames);reflexivity.
  - assert (HU:forall i,code_value env(source_parameter_up names i)=i).
    { intros [|i];cbn [source_parameter_up code_value];[reflexivity|].
      rewrite HNames. lia. }
    destruct q;cbn [source_parameter_expression sf_encode]; rewrite sf_make_value;
      rewrite (IHphi (source_parameter_up names) env HU);reflexivity.
Qed.

Theorem source_parameter_identity_numeral {ff} M
    (phi:@Core.form sig_empty ZFSignature.ZF_pred_sig full_operators ff):
  code_relation M(fun _=>zeroM M)(source_parameter_expression CEconst phi)
    (code_numeral M(sf_encode phi)).
Proof.
  rewrite <- (source_parameter_identity_value phi CEconst (fun _=>0) ltac:(intro i;reflexivity)).
  exact(code_relation_numeral M(fun _=>0)(source_parameter_expression CEconst phi)).
Qed.

Print Assumptions source_parameter_identity_value.
Print Assumptions source_parameter_identity_numeral.
