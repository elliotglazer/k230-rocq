(** The pinned legacy relativization has exactly the same syntax as the
    arithmetic source transform calibrated in SourceRelativizationCalibration. *)
From PAModel Require Import OldNamedSyntaxBridge OldFullNDSourceBridge
  SourceRelativizationCalibration.
From OldRegCon Require Rel.
Unset Implicit Arguments.

Theorem isolated_relativization {ff} (domain:isolated_old_form OC.falsity_on)
    (phi:isolated_old_form ff) :
  isolated_formula (@OldRegCon.Rel.rel OldUndecidability.FOL.Syntax.BinSig.sig_empty
    OldUndecidability.FOL.Sets.Signatures.ZFSignature.ZF_pred_sig domain ff phi) =
  sf_relativize (isolated_formula domain) (isolated_formula phi).
Proof.
  induction phi as [|ff P v|ff op a IHa b IHb|ff q a IH].
  - reflexivity.
  - destruct P;reflexivity.
  - cbn [OldRegCon.Rel.rel isolated_formula sf_relativize]. now rewrite IHa,IHb.
  - destruct q;cbn [OldRegCon.Rel.rel isolated_formula isolated_quant sf_relativize];
      now rewrite IH.
Qed.

Print Assumptions isolated_relativization.
