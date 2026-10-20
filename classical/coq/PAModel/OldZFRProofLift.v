(** Fixed finite proofs over the pinned ZFR axioms become actual numerical
    source proofs in every PA model. No internal formula is decoded here. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  OldNamedSyntaxBridge OldFullNDSourceBridge OldSetTheoryAxiomBridge
  SourceFiniteContexts SourceNumeralLift NumericalContexts NumericalSourceFull
  NumericalZFRAxioms SourceZFRProvability.
From OldZFC Require Z_prim.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Theorem finite_old_zfr_proof_lift M
    (A:list (isolated_old_form OC.falsity_on)) phi :
  (forall a,In a A -> OldZFC.Z_prim.ZFR a) ->
  @OND.prv OldUndecidability.FOL.Syntax.BinSig.sig_empty
    OS.ZFSignature.ZF_pred_sig OC.falsity_on OC.class A phi ->
  source_zfr_provable M (code_numeral M (sf_encode (isolated_formula phi))).
Proof.
  intros HA HP.
  destruct (source_model_context_total M (List.map isolated_formula A))
    as [b [c [n HC]]].
  exists b,c,n. split.
  - intros f HF.
    apply (proj1 (source_model_context_member_iff M b c n
      (List.map isolated_formula A) f HC)) in HF.
    destruct HF as [a [HIn ->]].
    apply List.in_map_iff in HIn. destruct HIn as [olda [<- HIn]].
    apply old_zfr_axiom_lift,HA,HIn.
  - exact (isolated_fullnd_forward_model M A phi HP b c n HC).
Qed.

Print Assumptions finite_old_zfr_proof_lift.
