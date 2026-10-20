(** The constructible-set class is nonempty provably in the actual numerical
    ZFR source theory, with all finite background axioms discharged. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  OldNamedSyntaxBridge OldFullNDSourceBridge OldSetTheoryAxiomBridge OldZFRProofLift SourceLFixed
  NumericalContexts NumericalSourceFull SourceZFRProvability SourceNumeralLift.
From OldZFC Require Z_prim Z_L.
From OldZF Require Std_iface.
From OldRegCon Require MinZF.
From OldUndecidability.FOL.Sets Require minZF.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Theorem old_L_background_valid a :
  In a old_L_background -> OldZFC.Z_prim.ZFR a.
Proof.
  intros [<-|[<-|H]].
  - right. reflexivity.
  - left;right. reflexivity.
  - apply in_app_iff in H as [H|H].
    + left;left. apply OldZF.Std_iface.ZF0_base,H.
    + apply OldZFC.Z_L.Ax_L_ok,H.
Qed.

Theorem numerical_L_nonempty_zfr M :
  source_zfr_provable M (source_L_nonempty_code M).
Proof.
  destruct (numerical_L_nonempty_context M) as [b [c [n [HC HP]]]].
  exists b,c,n. split;[|exact HP].
  intros f HF.
  apply (proj1 (source_model_context_member_iff M b c n source_L_background f HC)) in HF.
  destruct HF as [a [HIn ->]].
  apply List.in_map_iff in HIn. destruct HIn as [olda [<- HIn]].
  apply old_zfr_axiom_lift,old_L_background_valid,HIn.
Qed.

Print Assumptions old_L_background_valid.
Print Assumptions numerical_L_nonempty_zfr.
